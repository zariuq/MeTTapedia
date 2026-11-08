import Mettapedia.Languages.CHR.MachineScan

/-! The simulation relation between the refined CHR machine and the refined
operational semantics. Store contents agree up to permutation; seeds stand
for top-level tells; goal lists agree up to bindings; a scan stands for the
operational scan at the cursor of its next occurrence; a search stands for
the operational scan at its occurrence, with every selection it has already
passed rejected. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

inductive StatusRel : Status → CHR.Status → Prop where
  | running : StatusRel .running .running
  | failed : StatusRel .failed .failed
  | faulted (reason : ArithmeticFault) : StatusRel (.faulted reason) (.fault reason)

inductive TaskRel (program : Program) (store : Store) (history : List CHR.Key) (next : Nat) :
    Task → CHR.Task → Prop where
  | seeds (heads : List Head) (ground : ∀ head ∈ heads, (instantiateTerms [] head.arguments).isSome) :
      TaskRel program store history next (.seeds heads) (.goals [] (heads.map Goal.tell))
  | goals (environment other : Environment) (goals : List Goal) (agree : Agree environment other) :
      TaskRel program store history next (.goals environment goals) (.goals other goals)
  | scan (active : Nat) (key : Key) (values : List Value) (cursor : Nat)
      (below : active < next) (stored : ActiveStored store active key values) :
      TaskRel program store history next (.scan active key values (keyAtsFrom program key cursor))
        (.scan active cursor)
  | search (active : Nat) (key : Key) (values : List Value) (cursor : Nat) (occurrence : At)
      (frames : List Frame) (found : RuleOccurrence)
      (atCursor : (occurrences program)[cursor]? = some found)
      (matched : atOf program key found = some occurrence)
      (below : active < next) (stored : ActiveStored store active key values)
      (alive : lift key ⟨active, values⟩ ∈ contents store)
      (consumed : List (Environment × List Pick))
      (enumerated : consumed ++ pending store occurrence.head active values frames =
        selections store occurrence.head active values 0 occurrence.body.heads [] [] [])
      (rejected : ∀ selection ∈ consumed, Stale occurrence history selection ∨
        guardsEval selection.1 occurrence.body.guards = .ok false) :
      TaskRel program store history next
        (.search active key values occurrence (keyAtsFrom program key (cursor + 1)) frames) (.scan active cursor)

def Task.isSearch : Task → Bool
  | .search .. => true
  | _ => false

structure Simulates (program : Program) (state : State) (abstract : CHR.State) : Prop where
  store : abstract.store.Perm (contents state.store)
  coherent : Coherent state.store
  fresh : ∀ stored ∈ contents state.store, stored.id < state.next
  history : abstract.history = state.history
  next : abstract.nextId = state.next
  status : StatusRel state.status abstract.status
  tasks : state.status = .running →
    List.Forall₂ (TaskRel program state.store state.history state.next) state.tasks abstract.tasks
  shallow : ∀ task ∈ state.tasks.drop 1, task.isSearch = false

/-! ## Store changes keep the facts about other active constraints -/

theorem activeStored_add {store store' : Store} {active : Nat} {key : Key} {values : List Value}
    (stored : ActiveStored store active key values) (added : Occurrence)
    (grown : ∀ member, member ∈ contents store' ↔ member ∈ contents store ∨ member = added)
    (different : added.id ≠ active) : ActiveStored store' active key values := by
  refine ⟨stored.1, fun member inside same => ?_⟩
  rcases (grown member).mp inside with old | rfl
  · exact stored.2 member old same
  · exact absurd same different

theorem activeStored_remove {store store' : Store} {active : Nat} {key : Key} {values : List Value}
    (stored : ActiveStored store active key values)
    (shrunk : ∀ member, member ∈ contents store' → member ∈ contents store) : ActiveStored store' active key values :=
  ⟨stored.1, fun member inside same => stored.2 member (shrunk member inside) same⟩

theorem agree_refl (environment : Environment) : Agree environment environment := fun _ => rfl

theorem agree_cons {first second : Environment} (same : Agree first second) (index : Nat) (value : Value) :
    Agree ((index, value) :: first) ((index, value) :: second) := by
  intro other
  rw [lookup_cons, lookup_cons, same other]

theorem statusRel_running {status : CHR.Status} (related : StatusRel .running status) : status = .running := by
  cases related
  rfl

/-- A task other than a search stays related when a fresh occurrence is added
and the counter moves past it. -/
theorem taskRel_grow {program : Program} {store store' : Store} {history : List CHR.Key} {next : Nat}
    {task : Task} {abstractTask : CHR.Task} (related : TaskRel program store history next task abstractTask)
    (notSearch : task.isSearch = false) (added : Occurrence) (addedId : added.id = next)
    (grown : ∀ member, member ∈ contents store' ↔ member ∈ contents store ∨ member = added) :
    TaskRel program store' history (next + 1) task abstractTask := by
  cases related with
  | seeds heads ground => exact .seeds heads ground
  | goals environment other goals agree => exact .goals environment other goals agree
  | scan active key values cursor below stored =>
    exact .scan active key values cursor (by omega) (activeStored_add stored added grown (by omega))
  | search => simp [Task.isSearch] at notSearch

theorem forall₂_grow {program : Program} {store store' : Store} {history : List CHR.Key} {next : Nat}
    (added : Occurrence) (addedId : added.id = next)
    (grown : ∀ member, member ∈ contents store' ↔ member ∈ contents store ∨ member = added) :
    ∀ {tasks : List Task} {abstractTasks : List CHR.Task},
      List.Forall₂ (TaskRel program store history next) tasks abstractTasks →
      (∀ task ∈ tasks, task.isSearch = false) →
      List.Forall₂ (TaskRel program store' history (next + 1)) tasks abstractTasks
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons first rest, shallow =>
    .cons (taskRel_grow first (shallow _ List.mem_cons_self) added addedId grown)
      (forall₂_grow added addedId grown rest (fun task member => shallow task (List.mem_cons_of_mem _ member)))

theorem introduce_simulates (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (running : state.status = .running)
    (head : Head) (environment other : Environment) (agree : Agree environment other)
    (resume : Task) (goals : List Goal) (tail : List Task) (tailAbstract : List CHR.Task) (seeds : List Nat)
    (abstractTasks : abstract.tasks = .goals other (.tell head :: goals) :: tailAbstract)
    (machineTasks : state.tasks.drop 1 = tail)
    (resumeRel : TaskRel program state.store state.history state.next resume (.goals other goals))
    (resumeNotSearch : resume.isSearch = false)
    (tailRel : List.Forall₂ (TaskRel program state.store state.history state.next) tail tailAbstract) :
    ∃ abstract', Relation.ReflTransGen (Step program) abstract abstract' ∧
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
      Relation.ReflTransGen.single (Step.tellFault abstract other head goals tailAbstract abstractTasks
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
      Relation.ReflTransGen.single (Step.introduce abstract other head goals tailAbstract _ abstractTasks
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

#print axioms introduce_simulates

#print axioms activeStored_add

end Mettapedia.Languages.CHR.Machine
