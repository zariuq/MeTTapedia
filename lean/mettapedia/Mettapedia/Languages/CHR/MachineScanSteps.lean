import Mettapedia.Languages.CHR.MachineGoalSteps

/-! Scan ticks. A removed active constraint ends its scan; otherwise the
operational scan skips the occurrences of other keys up to the machine's
next occurrence, or to the end, and a search starts there with every
selection of the occurrence pending. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

theorem alive_iff (id : Nat) : ∀ (occurrences : List Occ),
    alive id occurrences = true ↔ ∃ occurrence ∈ occurrences, occurrence.id = id
  | [] => by simp [alive]
  | first :: rest => by simp [alive, alive_iff id rest]

/-- A table entry names its rule and head position; the head has the key. -/
theorem atOf_some {program : Program} {key : Key} {found : RuleOccurrence} {occurrence : At}
    (matched : atOf program key found = some occurrence) :
    program.rules[found.rule]? = some occurrence.body ∧ occurrence.rule = found.rule ∧
      occurrence.head = found.head ∧
      ∃ head, occurrence.body.heads[found.head]? = some head ∧ Head.key head = key := by
  unfold atOf at matched
  cases ruleAt : program.rules[found.rule]? with
  | none => simp [ruleAt] at matched
  | some rule =>
    cases headAt : rule.heads[found.head]? with
    | none => simp [ruleAt, headAt] at matched
    | some head =>
      by_cases same : Head.key head = key
      · simp only [ruleAt, headAt, same, Option.bind_eq_bind, Option.bind_some, if_true,
          Option.some.injEq] at matched
        subst matched
        exact ⟨rfl, rfl, rfl, head, headAt, same⟩
      · simp [ruleAt, headAt, same] at matched

/-- The operational store holds the active constraint only with its key and values. -/
theorem abstract_active {program : Program} {state : State} {abstract : CHR.State}
    (simulates : Simulates program state abstract) {active : Nat} {key : Key} {values : List Value}
    (stored : ActiveStored state.store active key values) :
    ∀ occurrence ∈ abstract.store, occurrence.id = active → occurrence.constraint = ⟨key.1, values⟩ := by
  intro occurrence member same
  rw [stored.2 occurrence (simulates.store.subset member) same]
  rfl

theorem alive_lift {store : Store} {active : Nat} {key : Key} {values : List Value}
    (stored : ActiveStored store active key values) (living : alive active (slot key store) = true) :
    lift key ⟨active, values⟩ ∈ contents store := by
  obtain ⟨occurrence, inSlot, same⟩ := (alive_iff active _).mp living
  have inContents := member_of_slot inSlot
  have equal := stored.2 _ inContents same
  rw [← equal]
  exact inContents

theorem scan_simulates (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (running : state.status = .running)
    (active : Nat) (key : Key) (values : List Value) (cursor : Nat) (tail : List Task)
    (tailAbstract : List CHR.Task)
    (tasks : state.tasks = .scan active key values (keyAtsFrom program key cursor) :: tail)
    (abstractTasks : abstract.tasks = .scan active cursor :: tailAbstract)
    (below : active < state.next) (stored : ActiveStored state.store active key values)
    (tailRel : List.Forall₂ (TaskRel program state.store state.history state.next) tail tailAbstract) :
    ∃ abstract', Relation.ReflTransGen (Step program) abstract abstract' ∧
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
      have skipped := skip_until program key values active tailAbstract stored.1
        ((occurrences program).length - cursor) cursor abstract abstractTasks abstractRunning abstractStored others
      have ended : Step program
          { abstract with tasks := .scan active (cursor + ((occurrences program).length - cursor)) :: tailAbstract }
          { abstract with tasks := tailAbstract } :=
        Step.endScan _ active _ tailAbstract rfl abstractRunning (List.getElem?_eq_none_iff.mpr (by omega))
      refine ⟨{ abstract with tasks := tailAbstract }, skipped.tail ended, ?_⟩
      exact ⟨simulates.store, simulates.coherent, simulates.fresh, simulates.history, simulates.next,
        simulates.status, fun _ => tailRel, fun task inside => shallow task (List.mem_of_mem_drop inside)⟩
    | cons occurrence after =>
      obtain ⟨distance, before, found, atFound, matched, afterEq⟩ :=
        keyAtsFrom_cons program key ((occurrences program).length - cursor) cursor (Nat.le_refl _) occurrence after listed
      have skipped := skip_until program key values active tailAbstract stored.1 distance cursor abstract
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
      .single (Step.missingActive abstract active cursor tailAbstract abstractTasks abstractRunning missing), ?_⟩
    exact ⟨simulates.store, simulates.coherent, simulates.fresh, simulates.history, simulates.next,
      simulates.status, fun _ => tailRel, fun task inside => shallow task (List.mem_of_mem_drop inside)⟩

#print axioms atOf_some
#print axioms scan_simulates

end Mettapedia.Languages.CHR.Machine
