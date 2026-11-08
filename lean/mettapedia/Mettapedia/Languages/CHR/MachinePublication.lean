import Mettapedia.Languages.CHR.MachineTick

/-! Seed identifiers and publication. The machine posts the seeds in order;
the `k`-th posted identifier names the occurrence of the `k`-th seed, and an
occurrence with that identifier, while stored, is that seed's constraint.
Every other stored occurrence is new. Operational steps keep or drop stored
occurrences, or add ones with fresh identifiers. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

theorem step_store {program : Program} {first second : CHR.State} (step : Step program first second) :
    ∀ occurrence ∈ second.store, occurrence ∈ first.store ∨ first.nextId ≤ occurrence.id := by
  intro occurrence member
  cases step with
  | introduce environment head goals tail constraint tasks running grounded =>
    rcases List.mem_append.mp member with old | new
    · exact .inl old
    · rw [List.mem_singleton] at new
      subst new
      exact .inr (Nat.le_refl _)
  | fire active cursor tail found rule environment selection tasks running atCursor atRule matched =>
    left
    apply matched.1.symm.subset
    simp only [commit] at member
    rcases List.mem_append.mp member with kept | rest
    · exact List.mem_append_left _ (List.mem_append_left _ kept)
    · exact List.mem_append_right _ rest
  | _ => exact .inl member

theorem step_next {program : Program} {first second : CHR.State} (step : Step program first second) :
    first.nextId ≤ second.nextId := by
  cases step <;> simp [commit]

theorem steps_next {program : Program} {first second : CHR.State}
    (run : Relation.ReflTransGen (Step program) first second) : first.nextId ≤ second.nextId := by
  induction run with
  | refl => exact Nat.le_refl _
  | tail _ step ih => exact Nat.le_trans ih (step_next step)

theorem steps_store {program : Program} {first second : CHR.State}
    (run : Relation.ReflTransGen (Step program) first second) :
    ∀ occurrence ∈ second.store, occurrence ∈ first.store ∨ first.nextId ≤ occurrence.id := by
  induction run with
  | refl => exact fun occurrence member => .inl member
  | tail earlier step ih =>
    intro occurrence member
    rcases step_store step occurrence member with old | fresh
    · exact ih occurrence old
    · exact .inr (Nat.le_trans (steps_next earlier) fresh)

/-- A tick keeps or drops stored occurrences, or adds ones with fresh identifiers. -/
theorem tick_store (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) :
    ∀ occurrence ∈ contents (tick (table program) state).store,
      occurrence ∈ contents state.store ∨ state.next ≤ occurrence.id := by
  intro occurrence member
  obtain ⟨abstract', run, related⟩ := tick_simulates program state abstract simulates
  have inAbstract := related.store.symm.subset member
  rcases steps_store run occurrence inAbstract with old | fresh
  · exact .inl (simulates.store.subset old)
  · exact .inr (simulates.next ▸ fresh)

theorem tick_next (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) : state.next ≤ (tick (table program) state).next := by
  obtain ⟨abstract', run, related⟩ := tick_simulates program state abstract simulates
  rw [← simulates.next, ← related.next]
  exact steps_next run

/-! ## The shape of the task list -/

def Task.isSeeds : Task → Bool
  | .seeds _ => true
  | _ => false

theorem introduce_shape (table : Table) (head : Head) (environment : Environment) (resume : Task)
    (original rest : List Task) (state : State) (seeds : List Nat) (resumeNotSeeds : resume.isSeeds = false) :
    ∃ fresh, (∀ task ∈ fresh, task.isSeeds = false) ∧
      ((introduce table head environment resume original rest state seeds).tasks = fresh ++ rest ∨
        (introduce table head environment resume original rest state seeds).tasks = original) := by
  unfold introduce
  cases instantiateTerms environment head.arguments with
  | none => exact ⟨[], by simp, .inr rfl⟩
  | some values =>
    refine ⟨[.scan state.next (Head.key head) values (occurrencesOf (Head.key head) table), resume], ?_, .inl rfl⟩
    intro task inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl
    · rfl
    · exact resumeNotSeeds

theorem fire_shape (active : Nat) (key : Key) (values : List Value) (occurrence : At) (after : List At)
    (environment : Environment) (picks : List Pick) (rest : List Task) (state : State) :
    ∃ fresh, (∀ task ∈ fresh, task.isSeeds = false) ∧
      (fire active key values occurrence after environment picks rest state).tasks = fresh ++ rest := by
  unfold fire
  dsimp only
  split
  · exact ⟨[.goals environment occurrence.body.body], by simp [Task.isSeeds], rfl⟩
  · exact ⟨[.goals environment occurrence.body.body, .scan active key values (occurrence :: after)],
      by simp [Task.isSeeds], rfl⟩

/-- Fresh tasks pushed in place of the first one. -/
def Pushed (rest after : List Task) : Prop := ∃ fresh, (∀ other ∈ fresh, other.isSeeds = false) ∧ after = fresh ++ rest

theorem pushed_cons (task : Task) (rest : List Task) (notSeeds : task.isSeeds = false) :
    Pushed rest (task :: rest) :=
  ⟨[task], by simp [notSeeds], rfl⟩

theorem pushed_rest (rest : List Task) : Pushed rest rest := ⟨[], by simp, rfl⟩

theorem fire_pushed (active : Nat) (key : Key) (values : List Value) (occurrence : At) (after : List At)
    (environment : Environment) (picks : List Pick) (rest : List Task) (state : State) :
    Pushed rest (fire active key values occurrence after environment picks rest state).tasks := by
  obtain ⟨fresh, notSeeds, shaped⟩ := fire_shape active key values occurrence after environment picks rest state
  exact ⟨fresh, notSeeds, shaped⟩

theorem search_shape (active : Nat) (key : Key) (values : List Value) (occurrence : At) (after : List At)
    (frames : List Frame) (rest : List Task) (state : State) :
    (search active key values occurrence after frames rest state).seeds = state.seeds ∧
      Pushed rest (search active key values occurrence after frames rest state).tasks := by
  unfold search
  cases frames with
  | nil => exact ⟨rfl, pushed_cons _ rest (by rfl)⟩
  | cons frame below =>
    dsimp only
    cases frame.candidates with
    | nil => exact ⟨rfl, pushed_cons _ rest (by rfl)⟩
    | cons candidate others =>
      dsimp only
      split
      · exact ⟨rfl, pushed_cons _ rest (by rfl)⟩
      · cases frame.heads with
        | nil => exact ⟨rfl, pushed_cons _ rest (by rfl)⟩
        | cons head later =>
          dsimp only
          cases matchTerms head.arguments candidate.values frame.environment with
          | none => exact ⟨rfl, pushed_cons _ rest (by rfl)⟩
          | some bound =>
            dsimp only
            cases later with
            | nil =>
              unfold complete
              dsimp only
              split
              · exact ⟨rfl, pushed_cons _ rest (by rfl)⟩
              · cases guardsEval bound occurrence.body.guards with
                | error reason => exact ⟨rfl, pushed_cons _ rest (by rfl)⟩
                | ok holds =>
                  cases holds with
                  | true =>
                    exact ⟨by unfold fire; rfl, fire_pushed active key values occurrence after bound
                      (frame.picks ++ [⟨Head.key head, candidate.id⟩]) rest state⟩
                  | false => exact ⟨rfl, pushed_cons _ rest (by rfl)⟩
            | cons nextHead others' => exact ⟨rfl, pushed_cons _ rest (by rfl)⟩

/-- A tick on a task other than the seeds keeps the posted seeds, and keeps
every task or replaces that task by tasks other than seeds. -/
theorem tick_shape (table : Table) (state : State) (task : Task) (rest : List Task)
    (running : state.status = .running) (tasks : state.tasks = task :: rest) (notSeeds : task.isSeeds = false) :
    (tick table state).seeds = state.seeds ∧
      ((tick table state).tasks = state.tasks ∨ Pushed rest (tick table state).tasks) := by
  unfold tick
  rw [running, tasks]
  dsimp only
  cases task with
  | seeds heads => simp [Task.isSeeds] at notSeeds
  | goals environment goals =>
    cases goals with
    | nil => exact ⟨rfl, .inr (pushed_rest rest)⟩
    | cons current goals =>
      unfold goal
      cases current with
      | tell head =>
        dsimp only
        obtain ⟨fresh, notSeedsFresh, shaped⟩ := introduce_shape table head environment (.goals environment goals)
          (.goals environment (.tell head :: goals) :: rest) rest state state.seeds rfl
        refine ⟨by unfold introduce; split <;> rfl, ?_⟩
        rcases shaped with shaped | shaped
        · exact .inr ⟨fresh, notSeedsFresh, shaped⟩
        · exact .inl (shaped.trans tasks.symm |>.trans tasks)
      | assign index expression =>
        dsimp only
        split
        · exact ⟨rfl, .inl tasks⟩
        · split
          · exact ⟨rfl, .inr (pushed_cons _ rest (by rfl))⟩
          · split
            · exact ⟨rfl, .inr (pushed_cons _ rest (by rfl))⟩
            · exact ⟨rfl, .inl tasks⟩
      | fail => exact ⟨rfl, .inl tasks⟩
  | scan active key values remaining =>
    show (scan active key values remaining rest state).seeds = state.seeds ∧
      ((scan active key values remaining rest state).tasks = Task.scan active key values remaining :: rest ∨
        Pushed rest (scan active key values remaining rest state).tasks)
    unfold scan
    split
    · exact ⟨rfl, .inr (pushed_rest rest)⟩
    · cases remaining with
      | nil => exact ⟨rfl, .inr (pushed_rest rest)⟩
      | cons occurrence after =>
        dsimp only
        cases occurrence.body.kept ++ occurrence.body.removed with
        | nil => exact ⟨rfl, .inr (pushed_cons _ rest (by rfl))⟩
        | cons first later => exact ⟨rfl, .inr (pushed_cons _ rest (by rfl))⟩
  | search active key values occurrence after frames =>
    obtain ⟨seedsSame, pushed⟩ := search_shape active key values occurrence after frames rest state
    exact ⟨seedsSame, .inr pushed⟩

/-! ## Posting the seeds -/

/-- The seeds the machine has not posted yet, as the task that posts them. -/
def SeedsShape (constraints : List Constraint) (state : State) : Prop :=
  ∃ front, (∀ task ∈ front, task.isSeeds = false) ∧
    ((state.tasks = front ∧ state.seeds.length = constraints.length) ∨
      state.tasks = front ++ [.seeds ((constraints.drop state.seeds.length).map Constraint.asHead)])

/-- What the machine has posted: identifiers in posting order, each below the
counter, each naming its seed's occurrence while that occurrence is stored. -/
structure Posting (constraints : List Constraint) (state : State) : Prop where
  bounded : state.seeds.length ≤ constraints.length
  shape : SeedsShape constraints state
  below : ∀ id ∈ state.seeds, id < state.next
  stored : ∀ (index id : Nat) (constraint : Constraint), state.seeds.reverse[index]? = some id →
    constraints[index]? = some constraint →
    ∀ occurrence ∈ contents state.store, occurrence.id = id → occurrence.constraint = constraint

theorem start_posting (constraints : List Constraint) :
    Posting constraints (start (constraints.map Constraint.asHead)) where
  bounded := by simp [start]
  shape := ⟨[], by simp, .inr (by simp [start])⟩
  below := by simp [start]
  stored := by simp [start]

theorem asHead_instantiate (constraint : Constraint) :
    instantiateTerms [] constraint.asHead.arguments = some constraint.arguments := by
  simp only [Constraint.asHead, instantiateTerms_values]

theorem tick_posting (program : Program) (constraints : List Constraint) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (posting : Posting constraints state) :
    Posting constraints (tick (table program) state) := by
  have stored := tick_store program state abstract simulates
  have grown := tick_next program state abstract simulates
  cases running : state.status with
  | failed =>
    have same : tick (table program) state = state := by unfold tick; rw [running]
    rw [same]; exact posting
  | faulted reason =>
    have same : tick (table program) state = state := by unfold tick; rw [running]
    rw [same]; exact posting
  | running =>
    cases tasks : state.tasks with
    | nil =>
      have same : tick (table program) state = state := by unfold tick; rw [running, tasks]
      rw [same]; exact posting
    | cons task rest =>
      obtain ⟨front, frontFree, shaped⟩ := posting.shape
      cases seedsTask : task.isSeeds with
      | false =>
        obtain ⟨seedsSame, newTasks⟩ := tick_shape (table program) state task rest running tasks seedsTask
        -- the first task belongs to `front`
        obtain ⟨front', frontEq⟩ : ∃ front', front = task :: front' := by
          cases front with
          | nil =>
            rcases shaped with ⟨empty, _⟩ | single
            · rw [tasks] at empty; cases empty
            · rw [tasks] at single
              simp only [List.nil_append, List.cons.injEq] at single
              rw [single.1] at seedsTask
              simp [Task.isSeeds] at seedsTask
          | cons first others =>
            rcases shaped with ⟨equal, _⟩ | appended
            · rw [tasks] at equal
              exact ⟨others, by rw [(List.cons.inj equal).1]⟩
            · rw [tasks] at appended
              exact ⟨others, by rw [(List.cons.inj appended).1]⟩
        subst frontEq
        have restShape : (rest = front' ∧ state.seeds.length = constraints.length) ∨
            rest = front' ++ [.seeds ((constraints.drop state.seeds.length).map Constraint.asHead)] := by
          rcases shaped with ⟨equal, complete⟩ | appended
          · rw [tasks] at equal
            exact .inl ⟨(List.cons.inj equal).2, complete⟩
          · rw [tasks] at appended
            exact .inr (List.cons.inj appended).2
        have front'Free : ∀ other ∈ front', other.isSeeds = false :=
          fun other member => frontFree other (List.mem_cons_of_mem _ member)
        refine ⟨by rw [seedsSame]; exact posting.bounded, ?_, ?_, ?_⟩
        · rcases newTasks with unchanged | ⟨fresh, freshFree, pushed⟩
          · refine ⟨task :: front', frontFree, ?_⟩
            rw [unchanged, seedsSame, tasks]
            rcases restShape with ⟨restEq, complete⟩ | restEq
            · exact .inl ⟨by rw [restEq], complete⟩
            · exact .inr (by rw [restEq]; rfl)
          · refine ⟨fresh ++ front', ?_, ?_⟩
            · intro other member
              rcases List.mem_append.mp member with inFresh | inFront
              · exact freshFree other inFresh
              · exact front'Free other inFront
            · rw [pushed, seedsSame]
              rcases restShape with ⟨restEq, complete⟩ | restEq
              · exact .inl ⟨by rw [restEq], complete⟩
              · exact .inr (by rw [restEq, List.append_assoc])
        · intro id member
          rw [seedsSame] at member
          exact Nat.lt_of_lt_of_le (posting.below id member) grown
        · intro index id constraint posted indexed occurrence member same
          rw [seedsSame] at posted
          rcases stored occurrence member with old | fresh
          · exact posting.stored index id constraint posted indexed occurrence old same
          · exfalso
            have inSeeds : id ∈ state.seeds := List.mem_reverse.mp (List.mem_of_getElem? posted)
            have below := posting.below id inSeeds
            omega
      | true =>
        cases task with
        | goals => simp [Task.isSeeds] at seedsTask
        | scan => simp [Task.isSeeds] at seedsTask
        | search => simp [Task.isSeeds] at seedsTask
        | seeds heads =>
          -- the seeds task is the only task
          have only : rest = [] ∧ heads = (constraints.drop state.seeds.length).map Constraint.asHead := by
            cases front with
            | nil =>
              rcases shaped with ⟨empty, _⟩ | single
              · rw [tasks] at empty; cases empty
              · rw [tasks] at single
                simp only [List.nil_append, List.cons.injEq, Task.seeds.injEq] at single
                exact ⟨single.2, single.1⟩
            | cons first others =>
              exfalso
              have firstFree := frontFree first List.mem_cons_self
              rcases shaped with ⟨equal, _⟩ | appended
              · rw [tasks] at equal
                rw [← (List.cons.inj equal).1] at firstFree
                simp [Task.isSeeds] at firstFree
              · rw [tasks] at appended
                rw [← (List.cons.inj appended).1] at firstFree
                simp [Task.isSeeds] at firstFree
          obtain ⟨restEmpty, headsEq⟩ := only
          subst restEmpty
          cases heads with
          | nil =>
            have ticked : tick (table program) state = { state with tasks := [] } := by
              unfold tick; rw [running, tasks]
            rw [ticked]
            have complete : state.seeds.length = constraints.length := by
              have dropped : constraints.drop state.seeds.length = [] := by
                have := congrArg List.length headsEq
                simp only [List.length_nil, List.length_map, List.length_drop] at this
                exact List.drop_eq_nil_of_le (by omega)
              have := posting.bounded
              have lengthDrop := congrArg List.length dropped
              simp only [List.length_drop, List.length_nil] at lengthDrop
              omega
            exact ⟨posting.bounded, ⟨[], by simp, .inl ⟨rfl, complete⟩⟩, posting.below, posting.stored⟩
          | cons head heads =>
            have ticked : tick (table program) state =
                introduce (table program) head [] (.seeds heads) state.tasks [] state (state.next :: state.seeds) := by
              unfold tick; rw [running, tasks]
            -- the seed being posted
            obtain ⟨constraint, indexed, headIs, headsIs⟩ : ∃ constraint,
                constraints[state.seeds.length]? = some constraint ∧ head = constraint.asHead ∧
                heads = (constraints.drop (state.seeds.length + 1)).map Constraint.asHead := by
              cases dropped : constraints.drop state.seeds.length with
              | nil => rw [dropped] at headsEq; cases headsEq
              | cons first others =>
                rw [dropped, List.map_cons, List.cons.injEq] at headsEq
                refine ⟨first, ?_, headsEq.1, ?_⟩
                · have := List.getElem?_drop (xs := constraints) (i := state.seeds.length) (j := 0)
                  rw [dropped, Nat.add_zero] at this
                  simpa using this.symm
                · rw [headsEq.2, ← List.drop_drop, dropped]
                  rfl
            have instantiated : instantiateTerms [] head.arguments = some constraint.arguments := by
              rw [headIs]; exact asHead_instantiate constraint
            rw [ticked]
            unfold introduce
            rw [instantiated]
            dsimp only
            have lengthBound : state.seeds.length < constraints.length :=
              (List.getElem?_eq_some_iff.mp indexed).1
            have freshId : state.next ∉ (contents state.store).map Occurrence.id := by
              intro inside
              obtain ⟨member, inStore, same⟩ := List.mem_map.mp inside
              have := simulates.fresh member inStore
              omega
            have arity : constraint.arguments.length = (Head.key head).2 := by
              rw [headIs]; simp [Head.key, Constraint.asHead]
            obtain ⟨_, perm'⟩ := introduce_store state.store simulates.coherent (Head.key head)
              ⟨state.next, constraint.arguments⟩ freshId arity
            refine ⟨by simp only [List.length_cons]; omega, ?_, ?_, ?_⟩
            · refine ⟨[.scan state.next (Head.key head) constraint.arguments
                  (occurrencesOf (Head.key head) (table program))], by simp [Task.isSeeds], .inr ?_⟩
              rw [headsIs]
              simp
            · intro id member
              simp only [List.mem_cons] at member
              rcases member with rfl | old
              · exact Nat.lt_succ_self _
              · exact Nat.lt_succ_of_lt (posting.below id old)
            · intro index id posted indexedPosted postedAt occurrence member same
              simp only [List.reverse_cons] at indexedPosted
              have inNew := perm'.subset member
              rcases List.mem_append.mp inNew with old | new
              · -- an old occurrence: its identifier is below the counter
                by_cases earlier : index < state.seeds.length
                · rw [List.getElem?_append_left (by simpa using earlier)] at indexedPosted
                  exact posting.stored index id posted indexedPosted postedAt occurrence old same
                · have atEnd : index = state.seeds.length := by
                    have bound := (List.getElem?_eq_some_iff.mp indexedPosted).1
                    simp at bound
                    omega
                  subst atEnd
                  rw [List.getElem?_append_right (by simp), List.length_reverse, Nat.sub_self] at indexedPosted
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at indexedPosted
                  have := simulates.fresh occurrence old
                  omega
              · rw [List.mem_singleton] at new
                subst new
                by_cases earlier : index < state.seeds.length
                · rw [List.getElem?_append_left (by simpa using earlier)] at indexedPosted
                  exfalso
                  have inSeeds : id ∈ state.seeds := List.mem_reverse.mp (List.mem_of_getElem? indexedPosted)
                  have := posting.below id inSeeds
                  simp only [lift] at same
                  omega
                · have atEnd : index = state.seeds.length := by
                    have bound := (List.getElem?_eq_some_iff.mp indexedPosted).1
                    simp at bound
                    omega
                  subst atEnd
                  rw [indexed, Option.some.injEq] at postedAt
                  subst postedAt
                  rw [headIs]
                  rfl

theorem advance_posting (program : Program) (constraints : List Constraint) :
    ∀ (budget : Nat) (state : State) (abstract : CHR.State), Simulates program state abstract →
      Posting constraints state → Posting constraints (advance (table program) budget state)
  | 0, _, _, _, posting => posting
  | budget + 1, state, abstract, simulates, posting => by
    unfold advance
    split
    · obtain ⟨middle, _, related⟩ := tick_simulates program state abstract simulates
      exact advance_posting program constraints budget _ middle related
        (tick_posting program constraints state abstract simulates posting)
    · exact posting

/-- **Publication.** In a run from the seeds of `constraints`, the `k`-th posted
identifier names the occurrence of the `k`-th constraint: every stored
occurrence with that identifier is that constraint. A completed run has
posted every seed. -/
theorem run_posting (program : Program) (constraints : List Constraint) (budget : Nat) :
    Posting constraints (advance (table program) budget (start (constraints.map Constraint.asHead))) :=
  advance_posting program constraints budget _ _ (start_simulates program constraints)
    (start_posting constraints)

theorem completed_posted (constraints : List Constraint) (state : State) (posting : Posting constraints state)
    (finished : state.tasks = []) : state.seeds.length = constraints.length := by
  obtain ⟨front, _, shaped⟩ := posting.shape
  rcases shaped with ⟨_, complete⟩ | appended
  · exact complete
  · rw [finished] at appended
    exact absurd appended.symm (by simp)

#print axioms tick_store
#print axioms run_posting
#print axioms completed_posted
#print axioms tick_shape
#print axioms tick_next

end Mettapedia.Languages.CHR.Machine
