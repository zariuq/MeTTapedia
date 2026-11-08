import Mettapedia.Languages.CHR.MachineCursor

/-! Scans across occurrences of other keys. Between two occurrences of the
active constraint's key, the operational scan skips every occurrence; past
the last one it skips to the end. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

/-- If an occurrence carries the active identifier, it is the active
constraint with its key and values. -/
def ActiveStored (store : Store) (active : Nat) (key : Key) (values : List Value) : Prop :=
  values.length = key.2 ∧ ∀ stored ∈ contents store, stored.id = active → stored = lift key ⟨active, values⟩

theorem skip_until (program : Program) (key : Key) (values : List Value) (active : Nat) (tail : List CHR.Task)
    (arity : values.length = key.2) :
    ∀ (distance cursor : Nat) (state : CHR.State),
      state.tasks = .scan active cursor :: tail → state.status = .running →
      (∀ stored ∈ state.store, stored.id = active → stored.constraint = ⟨key.1, values⟩) →
      (∀ offset < distance, ∃ occurrence, (occurrences program)[cursor + offset]? = some occurrence ∧
        atOf program key occurrence = none) →
      Relation.ReflTransGen (Step program) state { state with tasks := .scan active (cursor + distance) :: tail }
  | 0, cursor, state, tasks, _, _, _ => by
    have same : { state with tasks := CHR.Task.scan active (cursor + 0) :: tail } = state := by
      rw [Nat.add_zero, ← tasks]
    rw [same]
  | distance + 1, cursor, state, tasks, running, stored, others => by
    obtain ⟨occurrence, atCursor, other⟩ := others 0 (Nat.succ_pos _)
    rw [Nat.add_zero] at atCursor
    have first := skip_other_key program state active cursor tail key values tasks running occurrence atCursor
      other stored arity
    have rest := skip_until program key values active tail arity distance (cursor + 1)
      { state with tasks := .scan active (cursor + 1) :: tail } rfl running stored
      (fun offset bounded => by
        obtain ⟨later, atLater, otherLater⟩ := others (offset + 1) (by omega)
        exact ⟨later, by rwa [show cursor + 1 + offset = cursor + (offset + 1) by omega], otherLater⟩)
    have joined := Relation.ReflTransGen.head first rest
    simpa [show cursor + 1 + distance = cursor + (distance + 1) by omega] using joined

/-- The next occurrence of a key from a cursor: the occurrences before it
have other keys. -/
theorem keyAtsFrom_cons (program : Program) (key : Key) :
    ∀ (fuel cursor : Nat), (occurrences program).length - cursor ≤ fuel →
      ∀ (occurrence : At) (after : List At), keyAtsFrom program key cursor = occurrence :: after →
      ∃ distance, (∀ offset < distance, ∃ other, (occurrences program)[cursor + offset]? = some other ∧
          atOf program key other = none) ∧
        ∃ found, (occurrences program)[cursor + distance]? = some found ∧
          atOf program key found = some occurrence ∧ after = keyAtsFrom program key (cursor + distance + 1)
  | fuel, cursor, bounded, occurrence, after, listed => by
    cases atCursor : (occurrences program)[cursor]? with
    | none =>
      rw [keyAtsFrom_end program key cursor atCursor] at listed
      cases listed
    | some here =>
      rw [keyAtsFrom_succ program key cursor here atCursor] at listed
      cases matched : atOf program key here with
      | some entry =>
        rw [matched] at listed
        simp only [Option.toList_some, List.singleton_append, List.cons.injEq] at listed
        obtain ⟨rfl, rfl⟩ := listed
        exact ⟨0, by simp, here, by simpa using atCursor, matched, by simp⟩
      | none =>
        rw [matched] at listed
        simp only [Option.toList_none, List.nil_append] at listed
        cases fuel with
        | zero =>
          have long : (occurrences program).length ≤ cursor := by omega
          rw [List.getElem?_eq_none_iff.mpr long] at atCursor
          cases atCursor
        | succ smaller =>
          obtain ⟨distance, before, found, atFound, foundMatched, afterEq⟩ :=
            keyAtsFrom_cons program key smaller (cursor + 1) (by omega) occurrence after listed
          refine ⟨distance + 1, ?_, found, ?_, foundMatched, ?_⟩
          · intro offset less
            cases offset with
            | zero => exact ⟨here, by simpa using atCursor, matched⟩
            | succ offset =>
              obtain ⟨other, atOther, otherNone⟩ := before offset (by omega)
              exact ⟨other, by rwa [show cursor + (offset + 1) = cursor + 1 + offset by omega], otherNone⟩
          · rwa [show cursor + (distance + 1) = cursor + 1 + distance by omega]
          · rwa [show cursor + (distance + 1) + 1 = cursor + 1 + distance + 1 by omega]

/-- Past the last occurrence of a key, every occurrence has another key. -/
theorem keyAtsFrom_nil (program : Program) (key : Key) :
    ∀ (fuel cursor : Nat), (occurrences program).length - cursor ≤ fuel →
      keyAtsFrom program key cursor = [] →
      ∀ offset < (occurrences program).length - cursor, ∃ other,
        (occurrences program)[cursor + offset]? = some other ∧ atOf program key other = none
  | fuel, cursor, bounded, empty, offset, less => by
    have inRange : cursor < (occurrences program).length := by omega
    obtain ⟨here, atCursor⟩ : ∃ here, (occurrences program)[cursor]? = some here :=
      ⟨_, List.getElem?_eq_getElem inRange⟩
    rw [keyAtsFrom_succ program key cursor here atCursor] at empty
    cases matched : atOf program key here with
    | some entry => rw [matched] at empty; simp at empty
    | none =>
      rw [matched] at empty
      simp only [Option.toList_none, List.nil_append] at empty
      cases offset with
      | zero => exact ⟨here, by simpa using atCursor, matched⟩
      | succ offset =>
        cases fuel with
        | zero => omega
        | succ smaller =>
          obtain ⟨other, atOther, otherNone⟩ :=
            keyAtsFrom_nil program key smaller (cursor + 1) (by omega) empty offset (by omega)
          exact ⟨other, by rwa [show cursor + (offset + 1) = cursor + 1 + offset by omega], otherNone⟩

#print axioms skip_until
#print axioms keyAtsFrom_cons
#print axioms keyAtsFrom_nil

end Mettapedia.Languages.CHR.Machine
