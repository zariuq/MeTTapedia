import Mettapedia.Languages.CHR.MachineScanSteps

/-! Search ticks. A silent move, a stale selection and a selection whose
guards fail take no operational step; an exhausted search is the operational
skip; a faulting guard is the operational guard fault; a firing is the
operational commit, with the machine store's contents permuting the
committed store. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

theorem matches_perm {selection : Selection} {rule : Rule} {environment : Environment}
    {store store' : List Occurrence} (matched : selection.Matches rule environment store)
    (permuted : store'.Perm store) : selection.Matches rule environment store' :=
  ⟨permuted.trans matched.1, matched.2⟩

/-- A task other than a search stays related when occurrences are removed
and the history changes. -/
theorem taskRel_shrink {program : Program} {store store' : Store} {history history' : List CHR.Key}
    {next : Nat} {task : Task} {abstractTask : CHR.Task}
    (related : TaskRel program store history next task abstractTask) (notSearch : task.isSearch = false)
    (shrunk : ∀ member, member ∈ contents store' → member ∈ contents store) :
    TaskRel program store' history' next task abstractTask := by
  cases related with
  | seeds heads ground => exact .seeds heads ground
  | goals environment other goals agree => exact .goals environment other goals agree
  | scan active key values cursor below stored =>
    exact .scan active key values cursor below (activeStored_remove stored shrunk)
  | search => simp [Task.isSearch] at notSearch

theorem forall₂_shrink {program : Program} {store store' : Store} {history history' : List CHR.Key}
    {next : Nat} (shrunk : ∀ member, member ∈ contents store' → member ∈ contents store) :
    ∀ {tasks : List Task} {abstractTasks : List CHR.Task},
      List.Forall₂ (TaskRel program store history next) tasks abstractTasks →
      (∀ task ∈ tasks, task.isSearch = false) →
      List.Forall₂ (TaskRel program store' history' next) tasks abstractTasks
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons first rest, shallow =>
    .cons (taskRel_shrink first (shallow _ List.mem_cons_self) shrunk)
      (forall₂_shrink shrunk rest (fun task member => shallow task (List.mem_cons_of_mem _ member)))

theorem search_simulates (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (running : state.status = .running)
    (active : Nat) (key : Key) (values : List Value) (cursor : Nat) (occurrence : At) (frames : List Frame)
    (found : RuleOccurrence) (tail : List Task) (tailAbstract : List CHR.Task)
    (tasks : state.tasks =
      .search active key values occurrence (keyAtsFrom program key (cursor + 1)) frames :: tail)
    (abstractTasks : abstract.tasks = .scan active cursor :: tailAbstract)
    (atCursor : (occurrences program)[cursor]? = some found)
    (matched : atOf program key found = some occurrence)
    (below : active < state.next) (stored : ActiveStored state.store active key values)
    (alive : lift key ⟨active, values⟩ ∈ contents state.store)
    (consumed : List (Environment × List Pick))
    (enumerated : consumed ++ pending state.store occurrence.head active values frames =
      selections state.store occurrence.head active values 0 occurrence.body.heads [] [] [])
    (rejected : ∀ selection ∈ consumed, Stale occurrence state.history selection ∨
      guardsEval selection.1 occurrence.body.guards = .ok false)
    (tailRel : List.Forall₂ (TaskRel program state.store state.history state.next) tail tailAbstract) :
    ∃ abstract', Relation.ReflTransGen (Step program) abstract abstract' ∧
      Simulates program
        (search active key values occurrence (keyAtsFrom program key (cursor + 1)) frames tail state)
        abstract' := by
  have abstractRunning : abstract.status = .running := statusRel_running (running ▸ simulates.status)
  have shallow := tail_shallow simulates tasks
  obtain ⟨ruleAt, ruleEq, headEq, head, headAt, headKey⟩ := atOf_some matched
  have activeArguments : ∀ member ∈ contents state.store, member.id = active →
      member.constraint.arguments = values := by
    intro member inside same
    rw [stored.2 member inside same]
    rfl
  have activeHead : ∀ chosen, occurrence.body.heads[occurrence.head]? = some chosen →
      (⟨active, ⟨chosen.name, values⟩⟩ : Occurrence) ∈ contents state.store := by
    intro chosen chosenAt
    have same : chosen = head := by
      rw [headEq, headAt] at chosenAt
      exact (Option.some.inj chosenAt).symm
    have name : head.name = key.1 := by
      rw [← headKey]
      rfl
    rw [same, name]
    exact alive
  have positionValid : ∃ chosen, occurrence.body.heads[occurrence.head]? = some chosen :=
    ⟨head, by rw [headEq]; exact headAt⟩
  rw [search_move]
  have pendingMoved := pending_move state.store occurrence.head active values frames
  cases decision : move state.store occurrence.head active values frames with
  | silent next =>
    rw [decision] at pendingMoved
    refine ⟨abstract, .refl, ?_⟩
    exact ⟨simulates.store, simulates.coherent, simulates.fresh, simulates.history, simulates.next,
      simulates.status,
      fun _ => abstractTasks ▸ .cons (.search active key values cursor occurrence next found atCursor matched below stored alive
        consumed (by rw [pendingMoved]; exact enumerated) rejected) tailRel,
      fun task inside => shallow task (by simpa using inside)⟩
  | exhausted =>
    rw [decision] at pendingMoved
    have rejectedAll : ∀ selection ∈ selections state.store occurrence.head active values 0
        occurrence.body.heads [] [] [], Stale occurrence state.history selection ∨
          guardsEval selection.1 occurrence.body.guards = .ok false := by
      rw [← enumerated, pendingMoved, List.append_nil]
      exact rejected
    have unusable := exhausted_unusable state.store simulates.coherent occurrence state.history active values
      activeArguments rejectedAll abstract.store simulates.store
    have skipped := Step.skip abstract active cursor tailAbstract found occurrence.body abstractTasks
      abstractRunning atCursor ruleAt (fun environment selection selected activeAt => by
        rw [simulates.history, ← ruleEq]
        exact unusable environment selection selected (by rw [headEq]; exact activeAt))
    refine ⟨_, .single skipped, ?_⟩
    exact ⟨simulates.store, simulates.coherent, simulates.fresh, simulates.history, simulates.next,
      simulates.status, fun _ => .cons (.scan active key values (cursor + 1) below stored) tailRel,
      fun task inside => shallow task (by simpa using inside)⟩
  | produce environment picks stay =>
    rw [decision] at pendingMoved
    have member : (environment, picks) ∈ selections state.store occurrence.head active values 0
        occurrence.body.heads [] [] [] := by
      rw [← enumerated, pendingMoved]
      simp
    have consumedMore : (consumed ++ [(environment, picks)]) ++
        pending state.store occurrence.head active values stay =
          selections state.store occurrence.head active values 0 occurrence.body.heads [] [] [] := by
      rw [List.append_assoc, List.singleton_append, ← pendingMoved]
      exact enumerated
    dsimp only
    unfold complete
    dsimp only
    by_cases stale : occurrence.body.propagation ∧ (⟨occurrence.rule, ids picks⟩ : CHR.Key) ∈ state.history
    · rw [if_pos stale]
      refine ⟨abstract, .refl, ?_⟩
      exact ⟨simulates.store, simulates.coherent, simulates.fresh, simulates.history, simulates.next,
        simulates.status,
        fun _ => abstractTasks ▸ .cons (.search active key values cursor occurrence stay found atCursor matched below stored alive
          (consumed ++ [(environment, picks)]) consumedMore (fun selection inside => by
            rcases List.mem_append.mp inside with old | new
            · exact rejected selection old
            · rw [List.mem_singleton] at new
              subst new
              exact .inl stale)) tailRel,
        fun task inside => shallow task (by simpa using inside)⟩
    · rw [if_neg stale]
      obtain ⟨chosen, facts, idsEq, selected, activeAt⟩ :=
        reached_matches state.store simulates.coherent occurrence active values activeHead positionValid member
      have chosenIds : (leanOccurrences occurrence.body.heads chosen).map Occurrence.id = ids picks := by
        rw [leanOccurrences_ids _ _ facts.lengths, idsEq]
      have keyEq : (selectionOf occurrence.body state.store chosen).key found.rule =
          ⟨occurrence.rule, ids picks⟩ := by
        show (⟨found.rule, _⟩ : CHR.Key) = _
        rw [ruleEq]
        congr 1
        show ((leanOccurrences occurrence.body.heads chosen).take occurrence.body.kept.length ++
          (leanOccurrences occurrence.body.heads chosen).drop occurrence.body.kept.length).map Occurrence.id = _
        rw [List.take_append_drop, chosenIds]
      have fresh : (selectionOf occurrence.body state.store chosen).Fresh occurrence.body found.rule
          abstract.history := by
        intro empty inHistory
        apply stale
        refine ⟨by simp [Rule.propagation, empty], ?_⟩
        rw [keyEq, simulates.history] at inHistory
        exact inHistory
      have abstractMatches : (selectionOf occurrence.body state.store chosen).Matches occurrence.body
          environment abstract.store :=
        matches_perm selected simulates.store
      have abstractActive : (selectionOf occurrence.body state.store chosen).ActiveAt active found.head := by
        rw [← headEq]
        exact activeAt
      cases guarded : guardsEval environment occurrence.body.guards with
      | error reason =>
        dsimp only
        refine ⟨{ abstract with status := .fault reason },
          .single (Step.guardFault abstract active cursor tailAbstract found occurrence.body environment
            (selectionOf occurrence.body state.store chosen) reason abstractTasks abstractRunning atCursor ruleAt
            abstractMatches abstractActive fresh guarded), ?_⟩
        exact ⟨simulates.store, simulates.coherent, simulates.fresh, simulates.history, simulates.next,
          .faulted reason, (fun impossible => by simp at impossible),
          fun task inside => shallow task (by simpa using inside)⟩
      | ok holds =>
        cases holds with
        | false =>
          dsimp only
          refine ⟨abstract, .refl, ?_⟩
          exact ⟨simulates.store, simulates.coherent, simulates.fresh, simulates.history, simulates.next,
            simulates.status,
            fun _ => abstractTasks ▸ .cons (.search active key values cursor occurrence stay found atCursor matched below stored
              alive (consumed ++ [(environment, picks)]) consumedMore (fun selection inside => by
                rcases List.mem_append.mp inside with old | new
                · exact rejected selection old
                · rw [List.mem_singleton] at new
                  subst new
                  exact .inr guarded)) tailRel,
            fun task inside => shallow task (by simpa using inside)⟩
        | true =>
          dsimp only
          have step := Step.fire abstract active cursor tailAbstract found occurrence.body environment
            (selectionOf occurrence.body state.store chosen) abstractTasks abstractRunning atCursor ruleAt
            abstractMatches abstractActive fresh guarded
          refine ⟨_, .single step, ?_⟩
          obtain ⟨coherent', perm'⟩ := commit_store state.store simulates.coherent occurrence.body chosen
            facts.lengths facts.distinct facts.stored facts.arities
          have picksEq : chosenPicks occurrence.body.heads chosen = picks := facts.picks.symm
          rw [picksEq] at coherent' perm'
          have shrunk : ∀ member,
              member ∈ contents (removePicks (picks.drop occurrence.body.kept.length) state.store) →
                member ∈ contents state.store := by
            intro member inside
            apply selected.1.symm.subset
            have inSelection := perm'.subset inside
            simp only [List.mem_append] at inSelection ⊢
            rcases inSelection with kept | rest
            · exact .inl (.inl kept)
            · exact .inr rest
          have removedIds : ids (picks.drop occurrence.body.kept.length) =
              (selectionOf occurrence.body state.store chosen).removed.map Occurrence.id := by
            show (picks.drop _).map Pick.id =
              ((leanOccurrences occurrence.body.heads chosen).drop _).map Occurrence.id
            rw [List.map_drop, List.map_drop, chosenIds]
            rfl
          have removedActive : active ∈ ids (picks.drop occurrence.body.kept.length) ↔
              (selectionOf occurrence.body state.store chosen).removed.any
                (fun member => member.id == active) = true := by
            rw [removedIds]
            simp [List.any_eq_true]
          have entries : occurrence :: keyAtsFrom program key (cursor + 1) = keyAtsFrom program key cursor := by
            rw [keyAtsFrom_succ program key cursor found atCursor, matched]
            rfl
          refine ⟨perm'.symm, coherent', fun member inside => simulates.fresh member (shrunk member inside), ?_,
            simulates.next, simulates.status, fun _ => ?_, ?_⟩
          · show (if occurrence.body.removed.isEmpty then
                (selectionOf occurrence.body state.store chosen).key found.rule :: abstract.history
                else abstract.history) =
              (if occurrence.body.propagation then (⟨occurrence.rule, ids picks⟩ : CHR.Key) :: state.history
                else state.history)
            rw [keyEq, simulates.history]
            rfl
          · show List.Forall₂ _
              (.goals environment occurrence.body.body ::
                (if active ∈ ids (picks.drop occurrence.body.kept.length) then tail
                  else .scan active key values (occurrence :: keyAtsFrom program key (cursor + 1)) :: tail))
              (.goals environment occurrence.body.body ::
                (if (selectionOf occurrence.body state.store chosen).removed.any
                    (fun member => member.id == active) then tailAbstract
                  else .scan active cursor :: tailAbstract))
            by_cases removed : active ∈ ids (picks.drop occurrence.body.kept.length)
            · rw [if_pos removed, if_pos (removedActive.mp removed)]
              exact .cons (.goals _ _ _ (agree_refl _)) (forall₂_shrink shrunk tailRel shallow)
            · rw [if_neg removed, if_neg (fun inside => removed (removedActive.mpr inside))]
              refine .cons (.goals _ _ _ (agree_refl _)) (.cons ?_ (forall₂_shrink shrunk tailRel shallow))
              rw [entries]
              exact .scan active key values cursor below (activeStored_remove stored shrunk)
          · intro task inside
            have continued : task ∈ (if active ∈ ids (picks.drop occurrence.body.kept.length) then tail
                else .scan active key values (occurrence :: keyAtsFrom program key (cursor + 1)) :: tail) :=
              inside
            by_cases removed : active ∈ ids (picks.drop occurrence.body.kept.length)
            · rw [if_pos removed] at continued
              exact shallow task continued
            · rw [if_neg removed] at continued
              rcases List.mem_cons.mp continued with same | inTail
              · rw [same]
                rfl
              · exact shallow task inTail

#print axioms search_simulates

end Mettapedia.Languages.CHR.Machine
