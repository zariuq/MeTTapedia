import Mettapedia.Languages.CHR.PolicyStep
import Mettapedia.Languages.CHR.MachineRefinement
import Mettapedia.Languages.CHR.MachineSkip

/-! The newest-first refined semantics is deterministic up to the order of the
store and the order of bindings. The one exception is a scan whose active
constraint has left the store: it may skip occurrences before it is dropped,
and every such detour ends in the state that drops the scan at once.

`Reordered` relates states that differ only in those orders, and it is a
bisimulation of policy steps (`reordered_step`, `reordered_run`). Two policy steps from
a well-formed state that is not such a scan end in equivalent states
(`policy_deterministic`). A counted run to a stopped state can be re-rooted
at any first step (`follow`, `follow_many`): the new run is shorter, or it has
the same length and the detour measure `deadRank` drops. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR

open Machine (Agree agree_refl agree_cons instantiate_agree eval_agree guardsEval_agree)

/-! ## Equivalent states -/

/-- Tasks that differ only in the order of their bindings. -/
inductive TaskReordered : Task → Task → Prop
  | goals (environment other : Environment) (goals : List Goal) (agree : Agree environment other) :
      TaskReordered (.goals environment goals) (.goals other goals)
  | scan (active cursor : Nat) : TaskReordered (.scan active cursor) (.scan active cursor)

theorem TaskReordered.refl : (task : Task) → TaskReordered task task
  | .goals environment body => .goals environment environment body (agree_refl environment)
  | .scan active cursor => .scan active cursor

theorem TaskReordered.goals_left {environment : Environment} {goals : List Goal} {task : Task}
    (same : TaskReordered (.goals environment goals) task) : ∃ other, task = .goals other goals ∧ Agree environment other := by
  cases same
  exact ⟨_, rfl, by assumption⟩

theorem TaskReordered.scan_left {active cursor : Nat} {task : Task} (same : TaskReordered (.scan active cursor) task) :
    task = .scan active cursor := by
  cases same
  rfl

theorem TaskReordered.symm {first second : Task} (same : TaskReordered first second) : TaskReordered second first := by
  cases same with
  | goals environment other goals agree => exact .goals other environment goals fun index => (agree index).symm
  | scan active cursor => exact .scan active cursor

theorem TaskReordered.trans {first second third : Task} (one : TaskReordered first second) (two : TaskReordered second third) :
    TaskReordered first third := by
  cases one with
  | goals environment other goals agree =>
    obtain ⟨last, rfl, agree'⟩ := two.goals_left
    exact .goals environment last goals fun index => (agree index).trans (agree' index)
  | scan active cursor =>
    rw [two.scan_left]
    exact .scan active cursor

theorem scan_reordered {active active' : Nat} (same : active = active') (cursor : Nat) :
    TaskReordered (.scan active cursor) (.scan active' cursor) := by
  rw [same]
  exact .scan active' cursor

theorem tasks_refl : (tasks : List Task) → List.Forall₂ TaskReordered tasks tasks
  | [] => .nil
  | task :: rest => .cons (TaskReordered.refl task) (tasks_refl rest)

theorem tasks_symm {first second : List Task} (same : List.Forall₂ TaskReordered first second) :
    List.Forall₂ TaskReordered second first := by
  induction same with
  | nil => exact .nil
  | @cons _ _ _ _ head _ ih => exact .cons head.symm ih

theorem tasks_trans {first second third : List Task} (one : List.Forall₂ TaskReordered first second)
    (two : List.Forall₂ TaskReordered second third) : List.Forall₂ TaskReordered first third := by
  induction one generalizing third with
  | nil =>
    rw [List.forall₂_nil_left_iff.mp two]
    exact .nil
  | @cons _ _ _ _ head _ ih =>
    obtain ⟨_, _, head', rest, rfl⟩ := List.forall₂_cons_left_iff.mp two
    exact .cons (head.trans head') (ih rest)

/-- States that differ only in the order of the store and of bindings. -/
structure Reordered (first second : State) : Prop where
  store : first.store.Perm second.store
  history : first.history = second.history
  nextId : first.nextId = second.nextId
  status : first.status = second.status
  tasks : List.Forall₂ TaskReordered first.tasks second.tasks

theorem Reordered.refl (state : State) : Reordered state state :=
  ⟨List.Perm.refl _, rfl, rfl, rfl, tasks_refl _⟩

theorem Reordered.symm {first second : State} (same : Reordered first second) : Reordered second first :=
  ⟨same.store.symm, same.history.symm, same.nextId.symm, same.status.symm, tasks_symm same.tasks⟩

theorem Reordered.trans {first second third : State} (one : Reordered first second) (two : Reordered second third) :
    Reordered first third :=
  ⟨one.store.trans two.store, one.history.trans two.history, one.nextId.trans two.nextId,
    one.status.trans two.status, tasks_trans one.tasks two.tasks⟩

/-! ## Matching does not see the order of the store or of bindings -/

theorem Selection.Matches.perm {selection : Selection} {rule : Rule} {environment : Environment}
    {store other : List Occurrence} (matched : selection.Matches rule environment store) (perm : store.Perm other) :
    selection.Matches rule environment other :=
  ⟨perm.symm.trans matched.1, matched.2⟩

theorem NewestFirst.perm {rule : Rule} {index head active : Nat} {store other : List Occurrence}
    {history : List Key} {selection : Selection} (newest : NewestFirst rule index head active store history selection)
    (perm : store.Perm other) : NewestFirst rule index head active other history selection :=
  fun environment candidate matched activeHead fresh usable =>
    newest environment candidate (matched.perm perm.symm) activeHead fresh usable

theorem head_agree {first second : Environment} (same : Agree first second) (head : Head) :
    head.instantiate first = head.instantiate second := by
  have terms : Term.instantiate first = Term.instantiate second := funext (instantiate_agree same)
  unfold Head.instantiate
  rw [terms]

/-- A commit is determined by its kept and removed heads, by its remaining
store up to order, and by its bindings up to order. -/
theorem commit_reordered {first second : State} {tail tail' : List Task} (history : first.history = second.history)
    (nextId : first.nextId = second.nextId) (status : first.status = second.status)
    (tails : List.Forall₂ TaskReordered tail tail') (rule : Rule) (index : Nat) {environment other : Environment}
    (agree : Agree environment other) {selection selection' : Selection} (kept : selection.kept = selection'.kept)
    (removed : selection.removed = selection'.removed) (rest : selection.rest.Perm selection'.rest)
    (active cursor : Nat) :
    Reordered (commit first rule index environment selection active cursor tail)
      (commit second rule index other selection' active cursor tail') := by
  refine ⟨?_, ?_, nextId, status, ?_⟩
  · show (selection.kept ++ selection.rest).Perm (selection'.kept ++ selection'.rest)
    rw [kept]
    exact rest.append_left selection'.kept
  · show (if rule.removed.isEmpty then selection.key index :: first.history else first.history) =
      (if rule.removed.isEmpty then selection'.key index :: second.history else second.history)
    simp only [Selection.key, Selection.heads, kept, removed, history]
  · show List.Forall₂ TaskReordered (.goals environment rule.body ::
        (if selection.removed.any (fun occurrence => occurrence.id == active) then tail
          else .scan active cursor :: tail))
      (.goals other rule.body ::
        (if selection'.removed.any (fun occurrence => occurrence.id == active) then tail'
          else .scan active cursor :: tail'))
    rw [removed]
    refine .cons (.goals _ _ _ agree) ?_
    by_cases removedActive : selection'.removed.any (fun occurrence => occurrence.id == active) = true
    · rw [if_pos removedActive, if_pos removedActive]
      exact tails
    · rw [if_neg removedActive, if_neg removedActive]
      exact .cons (.scan _ _) tails

/-! ## Equivalence is a bisimulation -/

theorem reordered_step {program : Program} {first second next : State} (same : Reordered first second)
    (step : PolicyStep program first next) : ∃ next', PolicyStep program second next' ∧ Reordered next next' := by
  have related := same.tasks
  have running' : first.status = .running → second.status = .running := fun running => same.status ▸ running
  cases step with
  | endGoals environment tail tasks running =>
    rw [tasks] at related
    obtain ⟨task, rest, top, others, shape⟩ := List.forall₂_cons_left_iff.mp related
    obtain ⟨other, rfl, _⟩ := top.goals_left
    exact ⟨_, .endGoals second other rest shape (running' running),
      ⟨same.store, same.history, same.nextId, same.status, others⟩⟩
  | introduce environment head goals tail constraint tasks running grounded =>
    rw [tasks] at related
    obtain ⟨task, rest, top, others, shape⟩ := List.forall₂_cons_left_iff.mp related
    obtain ⟨other, rfl, agree⟩ := top.goals_left
    refine ⟨_, .introduce second other head goals rest constraint shape (running' running)
      ((head_agree agree head).symm.trans grounded), ?_⟩
    exact ⟨same.store.append (List.Perm.of_eq (by rw [same.nextId])), same.history, by rw [same.nextId],
      same.status, .cons (scan_reordered same.nextId 0) (.cons (.goals _ _ _ agree) others)⟩
  | tellFault environment head goals tail tasks running ungrounded =>
    rw [tasks] at related
    obtain ⟨task, rest, top, others, shape⟩ := List.forall₂_cons_left_iff.mp related
    obtain ⟨other, rfl, agree⟩ := top.goals_left
    exact ⟨_, .tellFault second other head goals rest shape (running' running)
      ((head_agree agree head).symm.trans ungrounded), ⟨same.store, same.history, same.nextId, rfl, same.tasks⟩⟩
  | assign environment index expression goals tail result tasks running evaluated compatible =>
    rw [tasks] at related
    obtain ⟨task, rest, top, others, shape⟩ := List.forall₂_cons_left_iff.mp related
    obtain ⟨other, rfl, agree⟩ := top.goals_left
    have compatible' : lookup other index = none ∨ lookup other index = some (.integer result) := by
      rw [← agree index]
      exact compatible
    exact ⟨_, .assign second other index expression goals rest result shape (running' running)
      ((eval_agree agree expression).symm.trans evaluated) compatible',
      ⟨same.store, same.history, same.nextId, same.status, .cons (.goals _ _ _ (agree_cons agree index _)) others⟩⟩
  | assignFailed environment index expression goals tail result old tasks running evaluated bound different =>
    rw [tasks] at related
    obtain ⟨task, rest, top, others, shape⟩ := List.forall₂_cons_left_iff.mp related
    obtain ⟨other, rfl, agree⟩ := top.goals_left
    exact ⟨_, .assignFailed second other index expression goals rest result old shape (running' running)
      ((eval_agree agree expression).symm.trans evaluated) ((agree index).symm.trans bound) different,
      ⟨same.store, same.history, same.nextId, rfl, same.tasks⟩⟩
  | assignFault environment index expression goals tail reason tasks running evaluated =>
    rw [tasks] at related
    obtain ⟨task, rest, top, others, shape⟩ := List.forall₂_cons_left_iff.mp related
    obtain ⟨other, rfl, agree⟩ := top.goals_left
    exact ⟨_, .assignFault second other index expression goals rest reason shape (running' running)
      ((eval_agree agree expression).symm.trans evaluated), ⟨same.store, same.history, same.nextId, rfl, same.tasks⟩⟩
  | fail environment goals tail tasks running =>
    rw [tasks] at related
    obtain ⟨task, rest, top, others, shape⟩ := List.forall₂_cons_left_iff.mp related
    obtain ⟨other, rfl, _⟩ := top.goals_left
    exact ⟨_, .fail second other goals rest shape (running' running),
      ⟨same.store, same.history, same.nextId, rfl, same.tasks⟩⟩
  | missingActive active cursor tail tasks running missing =>
    rw [tasks] at related
    obtain ⟨task, rest, top, others, shape⟩ := List.forall₂_cons_left_iff.mp related
    rw [top.scan_left] at shape
    exact ⟨_, .missingActive second active cursor rest shape (running' running)
      (fun occurrence member => missing occurrence (same.store.mem_iff.mpr member)),
      ⟨same.store, same.history, same.nextId, same.status, others⟩⟩
  | endScan active cursor tail tasks running finished =>
    rw [tasks] at related
    obtain ⟨task, rest, top, others, shape⟩ := List.forall₂_cons_left_iff.mp related
    rw [top.scan_left] at shape
    exact ⟨_, .endScan second active cursor rest shape (running' running) finished,
      ⟨same.store, same.history, same.nextId, same.status, others⟩⟩
  | skip active cursor tail occurrence rule tasks running atCursor atRule unusable =>
    rw [tasks] at related
    obtain ⟨task, rest, top, others, shape⟩ := List.forall₂_cons_left_iff.mp related
    rw [top.scan_left] at shape
    refine ⟨_, .skip second active cursor rest occurrence rule shape (running' running) atCursor atRule ?_,
      ⟨same.store, same.history, same.nextId, same.status, .cons (.scan _ _) others⟩⟩
    intro environment selection fits activeHead
    rw [← same.history]
    exact unusable environment selection (fits.perm same.store.symm) activeHead
  | fire active cursor tail occurrence rule environment selection tasks running atCursor atRule fits activeHead fresh
      guarded newest =>
    rw [tasks] at related
    obtain ⟨task, rest, top, others, shape⟩ := List.forall₂_cons_left_iff.mp related
    rw [top.scan_left] at shape
    have fresh' : selection.Fresh rule occurrence.rule second.history := by
      rw [← same.history]
      exact fresh
    have newest' : NewestFirst rule occurrence.rule occurrence.head active second.store second.history selection := by
      rw [← same.history]
      exact newest.perm same.store
    exact ⟨_, .fire second active cursor rest occurrence rule environment selection shape (running' running) atCursor
      atRule (fits.perm same.store) activeHead fresh' guarded newest',
      commit_reordered same.history same.nextId same.status others rule occurrence.rule (agree_refl environment)
        rfl rfl (List.Perm.refl _) active cursor⟩
  | guardFault active cursor tail occurrence rule environment selection reason tasks running atCursor atRule fits
      activeHead fresh fault newest =>
    rw [tasks] at related
    obtain ⟨task, rest, top, others, shape⟩ := List.forall₂_cons_left_iff.mp related
    rw [top.scan_left] at shape
    have fresh' : selection.Fresh rule occurrence.rule second.history := by
      rw [← same.history]
      exact fresh
    have newest' : NewestFirst rule occurrence.rule occurrence.head active second.store second.history selection := by
      rw [← same.history]
      exact newest.perm same.store
    exact ⟨_, .guardFault second active cursor rest occurrence rule environment selection reason shape
      (running' running) atCursor atRule (fits.perm same.store) activeHead fresh' fault newest',
      ⟨same.store, same.history, same.nextId, rfl, same.tasks⟩⟩

/-- Policy runs counted by their steps. -/
inductive Run (program : Program) : Nat → State → State → Prop
  | done (state : State) : Run program 0 state state
  | step {first second last : State} {length : Nat} (head : PolicyStep program first second)
      (rest : Run program length second last) : Run program (length + 1) first last

theorem Run.of_reflTransGen {program : Program} {first last : State}
    (run : Relation.ReflTransGen (PolicyStep program) first last) : ∃ length, Run program length first last := by
  induction run using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .done _⟩
  | head step _ ih =>
    obtain ⟨length, rest⟩ := ih
    exact ⟨length + 1, .step step rest⟩

theorem reordered_run {program : Program} {first second last : State} {length : Nat} (same : Reordered first second)
    (run : Run program length first last) : ∃ last', Run program length second last' ∧ Reordered last last' := by
  induction run generalizing second with
  | done => exact ⟨second, .done _, same⟩
  | @step _ _ _ _ head _ ih =>
    obtain ⟨next', step', related⟩ := reordered_step same head
    obtain ⟨last', rest', final⟩ := ih related
    exact ⟨last', .step step' rest', final⟩

/-! ## Stopped states -/

/-- A state whose observation is final: failed, faulted or completed. -/
def Terminal (state : State) : Prop := observe state ≠ .pending

theorem observe_pending (state : State) : observe state = .pending ↔ state.status = .running ∧ state.tasks ≠ [] := by
  unfold observe
  cases state.status <;> cases state.tasks <;> simp

theorem PolicyStep.running {program : Program} {state next : State} (step : PolicyStep program state next) :
    state.status = .running := by
  cases step <;> assumption

theorem PolicyStep.busy {program : Program} {state next : State} (step : PolicyStep program state next) :
    ∃ task tail, state.tasks = task :: tail := by
  cases step <;> exact ⟨_, _, by assumption⟩

theorem PolicyStep.wellFormed {program : Program} {state next : State} (step : PolicyStep program state next)
    (formed : state.WellFormed) : next.WellFormed :=
  step.refined.wellFormed formed

theorem transGen_wellFormed {program : Program} {state later : State}
    (path : Relation.TransGen (PolicyStep program) state later) (formed : state.WellFormed) : later.WellFormed := by
  induction path with
  | single step => exact step.wellFormed formed
  | tail _ step ih => exact step.wellFormed ih

theorem terminal_stuck {program : Program} {state next : State} (stopped : Terminal state)
    (step : PolicyStep program state next) : False := by
  obtain ⟨task, tail, tasks⟩ := step.busy
  exact stopped ((observe_pending state).mpr ⟨step.running, by rw [tasks]; exact List.cons_ne_nil _ _⟩)

theorem terminal_reordered {first second : State} (same : Reordered first second) (stopped : Terminal first) :
    Terminal second := by
  intro pending
  obtain ⟨running, busy⟩ := (observe_pending second).mp pending
  refine stopped ((observe_pending first).mpr ⟨same.status.trans running, fun empty => busy ?_⟩)
  have lengths := same.tasks.length_eq
  rw [empty] at lengths
  exact List.eq_nil_of_length_eq_zero lengths.symm

/-! ## Determinism away from a dead scan -/

theorem newerIds_both_false {first second : List Nat} (one : PartnerSelection.newerIds first second = false)
    (two : PartnerSelection.newerIds second first = false) : first = second := by
  rcases PartnerSelection.newerIds_total first second with same | newer | older
  · exact same
  · rw [newer] at one
    cases one
  · rw [older] at two
    cases two

theorem heads_unique {store : List Occurrence} (unique : (store.map Occurrence.id).Nodup) :
    ∀ {first second : List Occurrence}, (∀ occurrence ∈ first, occurrence ∈ store) →
      (∀ occurrence ∈ second, occurrence ∈ store) → first.map Occurrence.id = second.map Occurrence.id →
        first = second
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, same => by simp at same
  | _ :: _, [], _, _, same => by simp at same
  | head :: rest, head' :: rest', inFirst, inSecond, same => by
    simp only [List.map_cons, List.cons.injEq] at same
    have equal : head = head' :=
      List.inj_on_of_nodup_map unique (inFirst head (by simp)) (inSecond head' (by simp)) same.1
    rw [equal, heads_unique unique (fun occurrence inside => inFirst occurrence (by simp [inside]))
      (fun occurrence inside => inSecond occurrence (by simp [inside])) same.2]

theorem forall₂_both {α β : Type} {one two : α → β → Prop} {heads : List α} {items : List β}
    (first : List.Forall₂ one heads items) (second : List.Forall₂ two heads items) :
    ∀ head ∈ heads, ∃ item, one head item ∧ two head item := by
  induction first with
  | nil => exact fun _ inside => absurd inside List.not_mem_nil
  | @cons head item _ _ related _ ih =>
    obtain ⟨related', rest⟩ := List.forall₂_cons.mp second
    intro other inside
    rcases List.mem_cons.mp inside with same | later
    · subst same
      exact ⟨item, related, related'⟩
    · exact ih rest other later

/-- Instantiating terms to the same values fixes their variables. -/
theorem instantiateTerms_determines {first second : Environment} {terms : List Term} {values : List Value}
    (one : Machine.instantiateTerms first terms = some values) (two : Machine.instantiateTerms second terms = some values)
    {index : Nat} (inside : index ∈ terms.flatMap Term.variables) : lookup first index = lookup second index := by
  have empty : ∀ target : Environment, Machine.Extends target [] := fun _ _ _ bound => by simp [lookup] at bound
  obtain ⟨bound, matched, firstGrown⟩ := Machine.matchTerms_complete terms values [] first (empty first) one
  obtain ⟨bound', matched', secondGrown⟩ := Machine.matchTerms_complete terms values [] second (empty second) two
  rw [matched] at matched'
  cases matched'
  obtain ⟨value, present⟩ := Option.isSome_iff_exists.mp
    (Machine.instantiateTerms_bound terms values (Machine.matchTerms_sound terms values [] bound matched).2 index inside)
  rw [firstGrown index value present, secondGrown index value present]

/-- Two matches of the same heads to the same occurrences bind alike. -/
theorem selection_agree {rule : Rule} {store : List Occurrence} {first second : Environment}
    {selection other : Selection} (one : selection.Matches rule first store) (two : other.Matches rule second store)
    (kept : selection.kept = other.kept) (removed : selection.removed = other.removed) : Agree first second := by
  intro index
  by_cases inRule : index ∈ rule.variables
  · simp only [Rule.variables, Rule.heads, List.mem_flatMap, List.mem_append] at inRule
    obtain ⟨head, member, inHead⟩ := inRule
    have both : ∃ occurrence : Occurrence, head.instantiate first = some occurrence.constraint ∧
        head.instantiate second = some occurrence.constraint := by
      rcases member with keptHead | removedHead
      · have twoKept := two.2.2.1
        rw [← kept] at twoKept
        exact forall₂_both one.2.2.1 twoKept head keptHead
      · have twoRemoved := two.2.2.2.1
        rw [← removed] at twoRemoved
        exact forall₂_both one.2.2.2.1 twoRemoved head removedHead
    obtain ⟨occurrence, firstHead, secondHead⟩ := both
    exact instantiateTerms_determines (Machine.head_instantiate_some firstHead).2
      (Machine.head_instantiate_some secondHead).2 inHead
  · have unbound : ∀ environment : Environment, (∀ binding ∈ environment, binding.1 ∈ rule.variables) →
        lookup environment index = none := by
      intro environment only
      cases present : lookup environment index with
      | none => rfl
      | some value => exact absurd (only _ (Machine.mem_of_lookup present)) inRule
    rw [unbound first one.2.2.2.2.2, unbound second two.2.2.2.2.2]

/-- Two newest usable selections take the same heads; their remaining stores
agree up to order and their bindings agree. -/
theorem newest_unique {rule : Rule} {index head active : Nat} {store : List Occurrence} {history : List Key}
    (unique : (store.map Occurrence.id).Nodup) {first second : Environment} {selection other : Selection}
    (matched : selection.Matches rule first store) (activeHead : selection.ActiveAt active head)
    (fresh : selection.Fresh rule index history) (usable : guardsEval first rule.guards ≠ .ok false)
    (newest : NewestFirst rule index head active store history selection)
    (matched' : other.Matches rule second store) (activeHead' : other.ActiveAt active head)
    (fresh' : other.Fresh rule index history) (usable' : guardsEval second rule.guards ≠ .ok false)
    (newest' : NewestFirst rule index head active store history other) :
    selection.kept = other.kept ∧ selection.removed = other.removed ∧ selection.rest.Perm other.rest ∧
      Agree first second := by
  have ids := newerIds_both_false (newest' first selection matched activeHead fresh usable)
    (newest second other matched' activeHead' fresh' usable')
  have inStore : ∀ (candidate : Selection) (environment : Environment), candidate.Matches rule environment store →
      ∀ occurrence ∈ candidate.heads, occurrence ∈ store := by
    intro candidate environment fits occurrence inside
    apply fits.1.mem_iff.mpr
    simp only [Selection.heads, List.mem_append] at inside ⊢
    tauto
  have heads : selection.kept ++ selection.removed = other.kept ++ other.removed :=
    heads_unique unique (inStore _ _ matched) (inStore _ _ matched') ids
  have lengths : selection.kept.length = other.kept.length :=
    matched.2.2.1.length_eq.symm.trans matched'.2.2.1.length_eq
  obtain ⟨kept, removed⟩ := List.append_inj heads lengths
  refine ⟨kept, removed, ?_, selection_agree matched matched' kept removed⟩
  have perm := matched.1.symm.trans matched'.1
  rw [kept, removed] at perm
  exact (List.perm_append_left_iff _).mp perm

/-- The step from a goal list. -/
def goalNext (state : State) (environment : Environment) (tail : List Task) : List Goal → State
  | [] => { state with tasks := tail }
  | .tell head :: goals =>
    match head.instantiate environment with
    | some constraint => { state with
        tasks := .scan state.nextId 0 :: .goals environment goals :: tail
        store := state.store ++ [⟨state.nextId, constraint⟩]
        nextId := state.nextId + 1 }
    | none => { state with status := .fault (.uninstantiated (.tuple head.arguments)) }
  | .assign index expression :: goals =>
    match expression.eval environment with
    | .error reason => { state with status := .fault reason }
    | .ok result =>
      if lookup environment index = none ∨ lookup environment index = some (.integer result) then
        { state with tasks := .goals ((index, .integer result) :: environment) goals :: tail }
      else { state with status := .failed }
  | .fail :: _ => { state with status := .failed }

/-- A step from a goal list is a function of the state. -/
theorem goals_next {program : Program} {state next : State} {environment : Environment} {goals : List Goal}
    {tail : List Task} (tasks : state.tasks = .goals environment goals :: tail) (step : PolicyStep program state next) :
    next = goalNext state environment tail goals := by
  cases step with
  | endGoals environment' tail' tasks' =>
    rw [tasks] at tasks'
    simp only [List.cons.injEq, Task.goals.injEq] at tasks'
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := tasks'
    rfl
  | introduce environment' head goals' tail' constraint tasks' _ grounded =>
    rw [tasks] at tasks'
    simp only [List.cons.injEq, Task.goals.injEq] at tasks'
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := tasks'
    simp only [goalNext, grounded]
  | tellFault environment' head goals' tail' tasks' _ ungrounded =>
    rw [tasks] at tasks'
    simp only [List.cons.injEq, Task.goals.injEq] at tasks'
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := tasks'
    simp only [goalNext, ungrounded]
  | assign environment' index expression goals' tail' result tasks' _ evaluated compatible =>
    rw [tasks] at tasks'
    simp only [List.cons.injEq, Task.goals.injEq] at tasks'
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := tasks'
    simp only [goalNext, evaluated]
    rw [if_pos compatible]
  | assignFailed environment' index expression goals' tail' result old tasks' _ evaluated bound different =>
    rw [tasks] at tasks'
    simp only [List.cons.injEq, Task.goals.injEq] at tasks'
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := tasks'
    have incompatible : ¬ (lookup environment index = none ∨
        lookup environment index = some (.integer result)) := by
      rw [bound]
      simp [different]
    simp only [goalNext, evaluated]
    rw [if_neg incompatible]
  | assignFault environment' index expression goals' tail' reason tasks' _ evaluated =>
    rw [tasks] at tasks'
    simp only [List.cons.injEq, Task.goals.injEq] at tasks'
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := tasks'
    simp only [goalNext, evaluated]
  | fail environment' goals' tail' tasks' =>
    rw [tasks] at tasks'
    simp only [List.cons.injEq, Task.goals.injEq] at tasks'
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := tasks'
    rfl
  | missingActive _ _ _ tasks' => rw [tasks] at tasks'; simp at tasks'
  | endScan _ _ _ tasks' => rw [tasks] at tasks'; simp at tasks'
  | skip _ _ _ _ _ tasks' => rw [tasks] at tasks'; simp at tasks'
  | fire _ _ _ _ _ _ _ tasks' => rw [tasks] at tasks'; simp at tasks'
  | guardFault _ _ _ _ _ _ _ _ tasks' => rw [tasks] at tasks'; simp at tasks'

/-- What a step from a scan of a stored active constraint can be. -/
theorem scan_cases {program : Program} {state next : State} {active cursor : Nat} {tail : List Task}
    (tasks : state.tasks = .scan active cursor :: tail) (alive : ∃ occurrence ∈ state.store, occurrence.id = active)
    (step : PolicyStep program state next) :
    ((occurrences program)[cursor]? = none ∧ next = { state with tasks := tail }) ∨
    ∃ occurrence rule, (occurrences program)[cursor]? = some occurrence ∧
      program.rules[occurrence.rule]? = some rule ∧
      (((∀ (environment : Environment) (selection : Selection),
          selection.Matches rule environment state.store → selection.ActiveAt active occurrence.head →
          ¬ selection.Fresh rule occurrence.rule state.history ∨ guardsEval environment rule.guards = .ok false) ∧
          next = { state with tasks := .scan active (cursor + 1) :: tail }) ∨
        ∃ environment selection, selection.Matches rule environment state.store ∧
          selection.ActiveAt active occurrence.head ∧ selection.Fresh rule occurrence.rule state.history ∧
          NewestFirst rule occurrence.rule occurrence.head active state.store state.history selection ∧
          ((guardsEval environment rule.guards = .ok true ∧
              next = commit state rule occurrence.rule environment selection active cursor tail) ∨
            ∃ reason, guardsEval environment rule.guards = .error reason ∧
              next = { state with status := .fault reason })) := by
  cases step with
  | endGoals _ _ tasks' => rw [tasks] at tasks'; simp at tasks'
  | introduce _ _ _ _ _ tasks' => rw [tasks] at tasks'; simp at tasks'
  | tellFault _ _ _ _ tasks' => rw [tasks] at tasks'; simp at tasks'
  | assign _ _ _ _ _ _ tasks' => rw [tasks] at tasks'; simp at tasks'
  | assignFailed _ _ _ _ _ _ _ tasks' => rw [tasks] at tasks'; simp at tasks'
  | assignFault _ _ _ _ _ _ tasks' => rw [tasks] at tasks'; simp at tasks'
  | fail _ _ _ tasks' => rw [tasks] at tasks'; simp at tasks'
  | missingActive active' cursor' tail' tasks' _ missing =>
    rw [tasks] at tasks'
    simp only [List.cons.injEq, Task.scan.injEq] at tasks'
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := tasks'
    obtain ⟨occurrence, member, named⟩ := alive
    exact absurd named (missing occurrence member)
  | endScan active' cursor' tail' tasks' _ finished =>
    rw [tasks] at tasks'
    simp only [List.cons.injEq, Task.scan.injEq] at tasks'
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := tasks'
    exact .inl ⟨finished, rfl⟩
  | skip active' cursor' tail' occurrence rule tasks' _ atCursor atRule unusable =>
    rw [tasks] at tasks'
    simp only [List.cons.injEq, Task.scan.injEq] at tasks'
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := tasks'
    exact .inr ⟨occurrence, rule, atCursor, atRule, .inl ⟨unusable, rfl⟩⟩
  | fire active' cursor' tail' occurrence rule environment selection tasks' _ atCursor atRule fits activeHead fresh
      guarded newest =>
    rw [tasks] at tasks'
    simp only [List.cons.injEq, Task.scan.injEq] at tasks'
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := tasks'
    exact .inr ⟨occurrence, rule, atCursor, atRule,
      .inr ⟨environment, selection, fits, activeHead, fresh, newest, .inl ⟨guarded, rfl⟩⟩⟩
  | guardFault active' cursor' tail' occurrence rule environment selection reason tasks' _ atCursor atRule fits
      activeHead fresh fault newest =>
    rw [tasks] at tasks'
    simp only [List.cons.injEq, Task.scan.injEq] at tasks'
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := tasks'
    exact .inr ⟨occurrence, rule, atCursor, atRule,
      .inr ⟨environment, selection, fits, activeHead, fresh, newest, .inr ⟨reason, fault, rfl⟩⟩⟩

theorem usable_of_end {environment : Environment} {guards : List Guard} {state next : State}
    {rule : Rule} {index : Nat} {selection : Selection} {active cursor : Nat} {tail : List Task}
    (finish : (guardsEval environment guards = .ok true ∧
        next = commit state rule index environment selection active cursor tail) ∨
      ∃ reason, guardsEval environment guards = .error reason ∧ next = { state with status := .fault reason }) :
    guardsEval environment guards ≠ .ok false := by
  rcases finish with ⟨guarded, _⟩ | ⟨reason, fault, _⟩
  · rw [guarded]
    exact fun same => by cases same
  · rw [fault]
    exact fun same => by cases same

theorem scan_deterministic {program : Program} {state first second : State} {active cursor : Nat}
    {tail : List Task} (formed : state.WellFormed) (tasks : state.tasks = .scan active cursor :: tail)
    (alive : ∃ occurrence ∈ state.store, occurrence.id = active)
    (one : PolicyStep program state first) (two : PolicyStep program state second) : Reordered first second := by
  rcases scan_cases tasks alive one with ⟨finished, rfl⟩ | ⟨occurrence, rule, atCursor, atRule, oneCase⟩ <;>
    rcases scan_cases tasks alive two with ⟨finished', rfl⟩ | ⟨occurrence', rule', atCursor', atRule', twoCase⟩
  · exact Reordered.refl _
  · rw [finished] at atCursor'
    cases atCursor'
  · rw [finished'] at atCursor
    cases atCursor
  · rw [atCursor] at atCursor'
    cases atCursor'
    rw [atRule] at atRule'
    cases atRule'
    rcases oneCase with ⟨unusable, rfl⟩ | ⟨environment, selection, fits, activeHead, fresh, newest, oneEnd⟩ <;>
      rcases twoCase with ⟨unusable', rfl⟩ | ⟨environment', selection', fits', activeHead', fresh', newest', twoEnd⟩
    · exact Reordered.refl _
    · exfalso
      rcases unusable environment' selection' fits' activeHead' with stale | rejected
      · exact stale fresh'
      · exact usable_of_end twoEnd rejected
    · exfalso
      rcases unusable' environment selection fits activeHead with stale | rejected
      · exact stale fresh
      · exact usable_of_end oneEnd rejected
    · obtain ⟨kept, removed, rest, agree⟩ := newest_unique formed.1 fits activeHead fresh (usable_of_end oneEnd)
        newest fits' activeHead' fresh' (usable_of_end twoEnd) newest'
      have sameGuards := guardsEval_agree agree rule.guards
      rcases oneEnd with ⟨guarded, rfl⟩ | ⟨reason, fault, rfl⟩ <;>
        rcases twoEnd with ⟨guarded', rfl⟩ | ⟨reason', fault', rfl⟩
      · exact commit_reordered rfl rfl rfl (tasks_refl _) rule occurrence.rule agree kept removed rest active cursor
      · rw [sameGuards, fault'] at guarded
        cases guarded
      · rw [sameGuards, guarded'] at fault
        cases fault
      · rw [sameGuards, fault'] at fault
        cases fault
        exact Reordered.refl _

/-- A scan whose active constraint has left the store. -/
def DeadTop (state : State) : Prop :=
  state.status = .running ∧ ∃ active cursor tail, state.tasks = .scan active cursor :: tail ∧
    ∀ occurrence ∈ state.store, occurrence.id ≠ active

/-- **Policy steps are deterministic up to order** from every well-formed
state whose next task is not a scan of a removed constraint. -/
theorem policy_deterministic {program : Program} {state first second : State} (formed : state.WellFormed)
    (awake : ¬ DeadTop state) (one : PolicyStep program state first) (two : PolicyStep program state second) :
    Reordered first second := by
  obtain ⟨task, tail, tasks⟩ := one.busy
  cases task with
  | goals environment goals =>
    rw [goals_next tasks one, goals_next tasks two]
    exact Reordered.refl _
  | scan active cursor =>
    have alive : ∃ occurrence ∈ state.store, occurrence.id = active := by
      by_contra absent
      simp only [not_exists, not_and] at absent
      exact awake ⟨one.running, active, cursor, tail, tasks, absent⟩
    exact scan_deterministic formed tasks alive one two

/-! ## Detours of a dead scan -/

/-- A scan of a removed constraint skips an occurrence or is dropped. -/
theorem dead_cases {program : Program} {state next : State} {active cursor : Nat} {tail : List Task}
    (tasks : state.tasks = .scan active cursor :: tail) (gone : ∀ occurrence ∈ state.store, occurrence.id ≠ active)
    (step : PolicyStep program state next) :
    next = { state with tasks := tail } ∨
      (next = { state with tasks := .scan active (cursor + 1) :: tail } ∧ cursor < (occurrences program).length) := by
  cases step with
  | endGoals _ _ tasks' => rw [tasks] at tasks'; simp at tasks'
  | introduce _ _ _ _ _ tasks' => rw [tasks] at tasks'; simp at tasks'
  | tellFault _ _ _ _ tasks' => rw [tasks] at tasks'; simp at tasks'
  | assign _ _ _ _ _ _ tasks' => rw [tasks] at tasks'; simp at tasks'
  | assignFailed _ _ _ _ _ _ _ tasks' => rw [tasks] at tasks'; simp at tasks'
  | assignFault _ _ _ _ _ _ tasks' => rw [tasks] at tasks'; simp at tasks'
  | fail _ _ _ tasks' => rw [tasks] at tasks'; simp at tasks'
  | missingActive active' cursor' tail' tasks' =>
    rw [tasks] at tasks'
    simp only [List.cons.injEq, Task.scan.injEq] at tasks'
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := tasks'
    exact .inl rfl
  | endScan active' cursor' tail' tasks' =>
    rw [tasks] at tasks'
    simp only [List.cons.injEq, Task.scan.injEq] at tasks'
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := tasks'
    exact .inl rfl
  | skip active' cursor' tail' occurrence rule tasks' _ atCursor =>
    rw [tasks] at tasks'
    simp only [List.cons.injEq, Task.scan.injEq] at tasks'
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := tasks'
    obtain ⟨inRange, _⟩ := List.getElem?_eq_some_iff.mp atCursor
    exact .inr ⟨rfl, inRange⟩
  | fire active' cursor' tail' occurrence rule environment selection tasks' _ _ _ fits activeHead =>
    rw [tasks] at tasks'
    simp only [List.cons.injEq, Task.scan.injEq] at tasks'
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := tasks'
    obtain ⟨member, found, named⟩ := activeHead
    have inHeads := List.mem_of_getElem? found
    refine absurd named (gone member (fits.1.mem_iff.mpr ?_))
    simp only [Selection.heads, List.mem_append] at inHeads ⊢
    tauto
  | guardFault active' cursor' tail' occurrence rule environment selection reason tasks' _ _ _ fits activeHead =>
    rw [tasks] at tasks'
    simp only [List.cons.injEq, Task.scan.injEq] at tasks'
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := tasks'
    obtain ⟨member, found, named⟩ := activeHead
    have inHeads := List.mem_of_getElem? found
    refine absurd named (gone member (fits.1.mem_iff.mpr ?_))
    simp only [Selection.heads, List.mem_append] at inHeads ⊢
    tauto

/-- Every run to a stopped state from a dead scan passes through the state
that drops it, in fewer steps. -/
theorem dead_run {program : Program} {length : Nat} {state final : State} (run : Run program length state final) :
    ∀ {active cursor : Nat} {tail : List Task}, state.status = .running →
      state.tasks = .scan active cursor :: tail → (∀ occurrence ∈ state.store, occurrence.id ≠ active) →
      Terminal final → ∃ shorter < length, Run program shorter { state with tasks := tail } final := by
  induction run with
  | done state =>
    intro active cursor tail running tasks _ stopped
    exact absurd ((observe_pending state).mpr ⟨running, by rw [tasks]; exact List.cons_ne_nil _ _⟩) stopped
  | @step first second last length head rest ih =>
    intro active cursor tail running tasks gone stopped
    rcases dead_cases tasks gone head with popped | ⟨skipped, _⟩
    · subst popped
      exact ⟨length, Nat.lt_succ_self _, rest⟩
    · subst skipped
      obtain ⟨shorter, less, rest'⟩ := ih running rfl gone stopped
      exact ⟨shorter, Nat.lt_succ_of_lt less, rest'⟩

/-- Drops on every detour of a dead scan. -/
def deadRank (program : Program) (state : State) : Nat :=
  ((occurrences program).length + 2) * state.tasks.length +
    match state.tasks with
    | .scan _ cursor :: _ => (occurrences program).length + 1 - cursor
    | _ => 0

/-- **Re-rooting a run at a first step.** A run to a stopped state can be
followed from any first step to an equivalent stopped state, in fewer steps,
or in as many steps while `deadRank` drops. -/
theorem follow {program : Program} {state next final : State} {length : Nat} (formed : state.WellFormed)
    (step : PolicyStep program state next) (run : Run program length state final) (stopped : Terminal final) :
    ∃ length' final', Run program length' next final' ∧ Reordered final final' ∧
      (length' < length ∨ (length' = length ∧ deadRank program next < deadRank program state)) := by
  by_cases dead : DeadTop state
  · obtain ⟨running, active, cursor, tail, tasks, gone⟩ := dead
    obtain ⟨shorter, less, rest⟩ := dead_run run running tasks gone stopped
    rcases dead_cases tasks gone step with popped | ⟨skipped, inRange⟩
    · subst popped
      exact ⟨shorter, final, rest, Reordered.refl _, .inl less⟩
    · subst skipped
      refine ⟨shorter + 1, final, .step (.missingActive _ active (cursor + 1) tail rfl running gone) rest,
        Reordered.refl _, ?_⟩
      have lower : deadRank program { state with tasks := .scan active (cursor + 1) :: tail } <
          deadRank program state := by
        simp only [deadRank, tasks, List.length_cons]
        exact Nat.add_lt_add_left (by omega) _
      omega
  · cases run with
    | done => exact (terminal_stuck stopped step).elim
    | step head rest =>
      obtain ⟨final', rest', related⟩ := reordered_run (policy_deterministic formed dead head step) rest
      exact ⟨_, final', rest', related, .inl (Nat.lt_succ_self _)⟩

/-- `follow` along several steps. -/
theorem follow_many {program : Program} {state later : State}
    (path : Relation.TransGen (PolicyStep program) state later) :
    ∀ {final : State} {length : Nat}, state.WellFormed → Run program length state final → Terminal final →
      ∃ length' final', Run program length' later final' ∧ Reordered final final' ∧
        (length' < length ∨ (length' = length ∧ deadRank program later < deadRank program state)) := by
  induction path with
  | single step => exact fun formed run stopped => follow formed step run stopped
  | tail path step ih =>
    intro final length formed run stopped
    obtain ⟨length', final', run', same, smaller⟩ := ih formed run stopped
    obtain ⟨length'', final'', run'', same', smaller'⟩ :=
      follow (transGen_wellFormed path formed) step run' (terminal_reordered same stopped)
    refine ⟨length'', final'', run'', same.trans same', ?_⟩
    omega

#print axioms policy_deterministic
#print axioms follow_many

end Mettapedia.Languages.CHR
