import Mettapedia.Languages.CHR.MachineCommit
import Mettapedia.Util.LinearHash
import Mettapedia.Languages.CHR.Refinement

/-! Occurrence cursors. The machine visits only the rule occurrences of the
active constraint's key; the operational scan steps through every rule
occurrence. `keyAtsFrom` lists the key's occurrences from a cursor on; the
table holds them from cursor zero. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

/-- The table entry of one rule occurrence, when its head has `key`. -/
def atOf (program : Program) (key : Key) (occurrence : RuleOccurrence) : Option At := do
  let rule ← program.rules[occurrence.rule]?
  let head ← rule.heads[occurrence.head]?
  if Head.key head = key then some ⟨occurrence.rule, occurrence.head, rule⟩ else none

/-- The occurrences of `key` from a cursor on. -/
def keyAtsFrom (program : Program) (key : Key) (cursor : Nat) : List At :=
  ((occurrences program).drop cursor).filterMap (atOf program key)

theorem table_entry (program : Program) (key : Key) :
    occurrencesOf key (table program) = keyAtsFrom program key 0 := by
  unfold table keyAtsFrom
  simp only [List.drop_zero]
  have unfolded : ∀ (keys : List Key), keys.Nodup → key ∈ keys ∨
      ((occurrences program).filterMap (atOf program key)) = [] →
      occurrencesOf key (keys.map fun candidate => (candidate, (occurrences program).filterMap fun occurrence => do
        let rule ← program.rules[occurrence.rule]?
        let head ← rule.heads[occurrence.head]?
        if Head.key head = candidate then some ⟨occurrence.rule, occurrence.head, rule⟩ else none)) =
        (occurrences program).filterMap (atOf program key) := by
    intro keys distinct present
    induction keys with
    | nil =>
      rcases present with absent | empty
      · cases absent
      · simp [occurrencesOf, empty]
    | cons first rest ih =>
      rw [List.nodup_cons] at distinct
      by_cases same : first = key
      · subst same
        simp only [List.map_cons, occurrencesOf, if_true]
        rfl
      · simp only [List.map_cons, occurrencesOf, same, if_false]
        apply ih distinct.2
        rcases present with inKeys | empty
        · rcases List.mem_cons.mp inKeys with equal | later
          · exact absurd equal.symm same
          · exact .inl later
        · exact .inr empty
  apply unfolded _ (Mettapedia.Util.LinearHash.eraseDups_nodup _)
  by_cases present : key ∈ (program.rules.flatMap fun rule => rule.heads.map Head.key).eraseDups
  · exact .inl present
  · right
    apply List.filterMap_eq_nil_iff.mpr
    intro occurrence _
    unfold atOf
    cases ruleAt : program.rules[occurrence.rule]? with
    | none => rfl
    | some rule =>
      cases headAt : rule.heads[occurrence.head]? with
      | none => simp [headAt]
      | some head =>
        have different : Head.key head ≠ key := by
          intro same
          apply present
          rw [List.mem_eraseDups, List.mem_flatMap]
          refine ⟨rule, List.mem_of_getElem? ruleAt, ?_⟩
          rw [List.mem_map]
          exact ⟨head, List.mem_of_getElem? headAt, same⟩
        simp [headAt, different]

theorem keyAtsFrom_succ (program : Program) (key : Key) (cursor : Nat) (occurrence : RuleOccurrence)
    (atCursor : (occurrences program)[cursor]? = some occurrence) :
    keyAtsFrom program key cursor =
      (atOf program key occurrence).toList ++ keyAtsFrom program key (cursor + 1) := by
  unfold keyAtsFrom
  have bound : cursor < (occurrences program).length := (List.getElem?_eq_some_iff.mp atCursor).1
  rw [List.drop_eq_getElem_cons bound]
  have same : (occurrences program)[cursor] = occurrence := (List.getElem?_eq_some_iff.mp atCursor).2
  rw [same, List.filterMap_cons]
  cases atOf program key occurrence <;> rfl

theorem keyAtsFrom_end (program : Program) (key : Key) (cursor : Nat)
    (beyond : (occurrences program)[cursor]? = none) : keyAtsFrom program key cursor = [] := by
  unfold keyAtsFrom
  have long : (occurrences program).length ≤ cursor := List.getElem?_eq_none_iff.mp beyond
  rw [List.drop_eq_nil_of_le long]
  rfl

/-- Every genuine rule occurrence names a rule and one of its heads. -/
theorem occurrence_valid (program : Program) (occurrence : RuleOccurrence)
    (member : occurrence ∈ occurrences program) :
    ∃ rule head, program.rules[occurrence.rule]? = some rule ∧ rule.heads[occurrence.head]? = some head := by
  unfold occurrences at member
  rw [List.mem_flatMap] at member
  obtain ⟨⟨rule, index⟩, inRules, inVisit⟩ := member
  rw [List.mem_map] at inVisit
  obtain ⟨head, inOrder, rfl⟩ := inVisit
  have ruleAt : program.rules[index]? = some rule := by
    rw [List.mem_zipIdx_iff_getElem?] at inRules
    simpa using inRules
  have inRange : head ∈ List.range rule.heads.length := (visitOrder_permutation rule).subset inOrder
  have bound : head < rule.heads.length := List.mem_range.mp inRange
  exact ⟨rule, rule.heads[head], ruleAt, List.getElem?_eq_getElem bound⟩

theorem forall₂_at {α β : Type} {relation : α → β → Prop} :
    ∀ {first : List α} {second : List β}, List.Forall₂ relation first second →
      ∀ {index : Nat} {left : α} {right : β}, first[index]? = some left → second[index]? = some right →
        relation left right
  | [], [], .nil, _, _, _, found, _ => by simp at found
  | _ :: _, _ :: _, .cons head rest, index, left, right, atLeft, atRight => by
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at atLeft atRight
      subst atLeft
      subst atRight
      exact head
    | succ index =>
      simp only [List.getElem?_cons_succ] at atLeft atRight
      exact forall₂_at rest atLeft atRight

/-- An occurrence whose head has another key than the active constraint can
be skipped: no selection can place the active constraint at that head. -/
theorem skip_other_key (program : Program) (state : CHR.State) (active cursor : Nat) (tail : List CHR.Task)
    (key : Key) (values : List Value)
    (tasks : state.tasks = .scan active cursor :: tail) (running : state.status = .running)
    (occurrence : RuleOccurrence) (atCursor : (occurrences program)[cursor]? = some occurrence)
    (other : atOf program key occurrence = none)
    (activeStored : ∀ stored ∈ state.store, stored.id = active → stored.constraint = ⟨key.1, values⟩)
    (arity : values.length = key.2) :
    Step program state { state with tasks := .scan active (cursor + 1) :: tail } := by
  obtain ⟨rule, head, ruleAt, headAt⟩ :=
    occurrence_valid program occurrence (List.mem_of_getElem? atCursor)
  have different : Head.key head ≠ key := by
    intro same
    simp [atOf, ruleAt, headAt, same] at other
  apply Step.skip state active cursor tail occurrence rule tasks running atCursor ruleAt
  intro environment selection matched activeAt
  exfalso
  obtain ⟨split, _, keptMatch, removedMatch, _, _⟩ := matched
  obtain ⟨chosen, chosenAt, isActive⟩ := activeAt
  have instantiated := forall₂_at (forall₂_append keptMatch removedMatch) headAt chosenAt
  have inStore : chosen ∈ state.store := by
    apply split.symm.subset
    have inHeads : chosen ∈ selection.heads := List.mem_of_getElem? chosenAt
    simp only [Selection.heads, List.mem_append] at inHeads ⊢
    rcases inHeads with kept | removed
    · exact .inl (.inl kept)
    · exact .inl (.inr removed)
  have stored := activeStored chosen inStore isActive
  rw [stored] at instantiated
  obtain ⟨sameName, arguments⟩ := head_instantiate_some instantiated
  rw [instantiateTerms_eq] at arguments
  have length := mapM_length arguments
  apply different
  simp only [Head.key] at sameName ⊢
  rw [sameName, ← length, arity]

#print axioms skip_other_key

#print axioms keyAtsFrom_succ
#print axioms occurrence_valid

#print axioms table_entry

end Mettapedia.Languages.CHR.Machine
