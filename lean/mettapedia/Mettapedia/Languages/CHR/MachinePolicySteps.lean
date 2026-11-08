import Mettapedia.Languages.CHR.MachineSearchSteps
import Mettapedia.Languages.CHR.MachinePolicy
import Mettapedia.Languages.CHR.PolicyStep

/-! The machine's search refines the newest-first policy. The search
simulation of `MachineSearchSteps` produces policy steps: when the machine
fires a selection or faults at one, no matching, fresh selection not rejected
by its guards is newer, because the enumeration is newest first and every
selection the search passed over was rejected. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

theorem search_simulates_policy (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (descending : Descending state.store) (running : state.status = .running)
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
    ∃ abstract', Relation.ReflTransGen (PolicyStep program) abstract abstract' ∧
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
    have skipped := PolicyStep.skip abstract active cursor tailAbstract found occurrence.body abstractTasks
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
      have newest : NewestFirst occurrence.body found.rule found.head active abstract.store abstract.history
          (selectionOf occurrence.body state.store chosen) := by
        intro otherEnvironment other otherMatches otherActive otherFresh otherGuards
        apply Bool.eq_false_iff.mpr
        intro newer
        have chosenHeads : (selectionOf occurrence.body state.store chosen).heads.map Occurrence.id = ids picks := by
          show ((leanOccurrences occurrence.body.heads chosen).take occurrence.body.kept.length ++
            (leanOccurrences occurrence.body.heads chosen).drop occurrence.body.kept.length).map Occurrence.id = _
          rw [List.take_append_drop, chosenIds]
        rw [chosenHeads] at newer
        have split : consumed ++ (environment, picks) :: pending state.store occurrence.head active values stay =
            selections state.store occurrence.head active values 0 occurrence.body.heads [] [] [] := by
          simpa [List.append_assoc] using consumedMore
        have sorted := selections_sorted state.store occurrence.head active values descending 0 occurrence.body.heads
          [] [] []
        have otherActive' : other.ActiveAt active occurrence.head := by rw [headEq]; exact otherActive
        have unusable := preferred_unusable state.store simulates.coherent occurrence state.history active values
          activeArguments (ids picks)
          (fun listed inside better => rejected listed (preferred_before sorted split listed inside better))
          abstract.store simulates.store otherEnvironment other otherMatches otherActive' newer
        rcases unusable with stale | rejectedGuards
        · apply stale
          rw [ruleEq, ← simulates.history]
          exact otherFresh
        · exact otherGuards rejectedGuards
      cases guarded : guardsEval environment occurrence.body.guards with
      | error reason =>
        dsimp only
        refine ⟨{ abstract with status := .fault reason },
          .single (PolicyStep.guardFault abstract active cursor tailAbstract found occurrence.body environment
            (selectionOf occurrence.body state.store chosen) reason abstractTasks abstractRunning atCursor ruleAt
            abstractMatches abstractActive fresh guarded newest), ?_⟩
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
          have step := PolicyStep.fire abstract active cursor tailAbstract found occurrence.body environment
            (selectionOf occurrence.body state.store chosen) abstractTasks abstractRunning atCursor ruleAt
            abstractMatches abstractActive fresh guarded newest
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

#print axioms search_simulates_policy

/-- Each search tick takes an operational step or lowers the search weight. -/
theorem search_progress (program : Program) (state : State) (abstract : CHR.State)
    (simulates : Simulates program state abstract) (descending : Descending state.store) (running : state.status = .running)
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
    (∃ abstract', Relation.TransGen (PolicyStep program) abstract abstract' ∧
      Simulates program
        (search active key values occurrence (keyAtsFrom program key (cursor + 1)) frames tail state)
        abstract') ∨
    (Simulates program (search active key values occurrence (keyAtsFrom program key (cursor + 1)) frames tail state)
        abstract ∧
      ∃ next, (search active key values occurrence (keyAtsFrom program key (cursor + 1)) frames tail state).tasks =
          .search active key values occurrence (keyAtsFrom program key (cursor + 1)) next :: tail ∧
        (search active key values occurrence (keyAtsFrom program key (cursor + 1)) frames tail state).store =
          state.store ∧
        weight state.store occurrence.head active values next < weight state.store occurrence.head active values frames)
      := by
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
    have shrinks := weight_move state.store occurrence.head active values frames
    rw [decision] at shrinks
    rw [decision] at pendingMoved
    refine .inr ⟨?_, _, rfl, rfl, shrinks⟩
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
    have skipped := PolicyStep.skip abstract active cursor tailAbstract found occurrence.body abstractTasks
      abstractRunning atCursor ruleAt (fun environment selection selected activeAt => by
        rw [simulates.history, ← ruleEq]
        exact unusable environment selection selected (by rw [headEq]; exact activeAt))
    refine .inl ⟨_, .single skipped, ?_⟩
    exact ⟨simulates.store, simulates.coherent, simulates.fresh, simulates.history, simulates.next,
      simulates.status, fun _ => .cons (.scan active key values (cursor + 1) below stored) tailRel,
      fun task inside => shallow task (by simpa using inside)⟩
  | produce environment picks stay =>
    have shrinks := weight_move state.store occurrence.head active values frames
    rw [decision] at shrinks
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
      refine .inr ⟨?_, _, rfl, rfl, shrinks⟩
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
      have newest : NewestFirst occurrence.body found.rule found.head active abstract.store abstract.history
          (selectionOf occurrence.body state.store chosen) := by
        intro otherEnvironment other otherMatches otherActive otherFresh otherGuards
        apply Bool.eq_false_iff.mpr
        intro newer
        have chosenHeads : (selectionOf occurrence.body state.store chosen).heads.map Occurrence.id = ids picks := by
          show ((leanOccurrences occurrence.body.heads chosen).take occurrence.body.kept.length ++
            (leanOccurrences occurrence.body.heads chosen).drop occurrence.body.kept.length).map Occurrence.id = _
          rw [List.take_append_drop, chosenIds]
        rw [chosenHeads] at newer
        have split : consumed ++ (environment, picks) :: pending state.store occurrence.head active values stay =
            selections state.store occurrence.head active values 0 occurrence.body.heads [] [] [] := by
          simpa [List.append_assoc] using consumedMore
        have sorted := selections_sorted state.store occurrence.head active values descending 0 occurrence.body.heads
          [] [] []
        have otherActive' : other.ActiveAt active occurrence.head := by rw [headEq]; exact otherActive
        have unusable := preferred_unusable state.store simulates.coherent occurrence state.history active values
          activeArguments (ids picks)
          (fun listed inside better => rejected listed (preferred_before sorted split listed inside better))
          abstract.store simulates.store otherEnvironment other otherMatches otherActive' newer
        rcases unusable with stale | rejectedGuards
        · apply stale
          rw [ruleEq, ← simulates.history]
          exact otherFresh
        · exact otherGuards rejectedGuards
      cases guarded : guardsEval environment occurrence.body.guards with
      | error reason =>
        dsimp only
        refine .inl ⟨{ abstract with status := .fault reason },
          .single (PolicyStep.guardFault abstract active cursor tailAbstract found occurrence.body environment
            (selectionOf occurrence.body state.store chosen) reason abstractTasks abstractRunning atCursor ruleAt
            abstractMatches abstractActive fresh guarded newest), ?_⟩
        exact ⟨simulates.store, simulates.coherent, simulates.fresh, simulates.history, simulates.next,
          .faulted reason, (fun impossible => by simp at impossible),
          fun task inside => shallow task (by simpa using inside)⟩
      | ok holds =>
        cases holds with
        | false =>
          dsimp only
          refine .inr ⟨?_, _, rfl, rfl, shrinks⟩
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
          have step := PolicyStep.fire abstract active cursor tailAbstract found occurrence.body environment
            (selectionOf occurrence.body state.store chosen) abstractTasks abstractRunning atCursor ruleAt
            abstractMatches abstractActive fresh guarded newest
          refine .inl ⟨_, .single step, ?_⟩
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

#print axioms search_progress

end Mettapedia.Languages.CHR.Machine
