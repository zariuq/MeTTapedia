import Mettapedia.Languages.CHR.MachineJudge

/-! An exhausted search licenses `Step.skip`. If the machine's search for a
rule occurrence ends with nothing fired, then every operational selection
with the active constraint at that head is already fired from, or fails its
guards, over any store that permutes the machine store's contents. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

mutual
  theorem instantiateTerm_bound {environment : Environment} :
      (term : Term) → (value : Value) → instantiateTerm environment term = some value →
        ∀ index ∈ term.variables, (lookup environment index).isSome
    | .value _, _, _ => by simp [Term.variables]
    | .var index, value, instantiated => by
      intro other member
      simp only [Term.variables, List.mem_singleton] at member
      subst member
      simp only [instantiateTerm] at instantiated
      simp [instantiated]
    | .tuple terms, value, instantiated => by
      simp only [instantiateTerm] at instantiated
      cases fields : instantiateTerms environment terms with
      | none => rw [fields] at instantiated; cases instantiated
      | some values =>
        intro index member
        simp only [Term.variables, List.mem_flatMap] at member
        exact instantiateTerms_bound terms values fields index (by simpa [List.mem_flatMap] using member)
  theorem instantiateTerms_bound {environment : Environment} :
      (terms : List Term) → (values : List Value) → instantiateTerms environment terms = some values →
        ∀ index ∈ terms.flatMap Term.variables, (lookup environment index).isSome
    | [], _, _ => by simp
    | term :: rest, values, instantiated => by
      simp only [instantiateTerms] at instantiated
      cases first : instantiateTerm environment term with
      | none => rw [first] at instantiated; cases instantiated
      | some value =>
        rw [first] at instantiated
        cases others : instantiateTerms environment rest with
        | none => rw [others] at instantiated; cases instantiated
        | some fields =>
          intro index member
          rw [List.flatMap_cons, List.mem_append] at member
          rcases member with here | later
          · exact instantiateTerm_bound term value first index here
          · exact instantiateTerms_bound rest fields others index later
end

theorem mem_of_lookup {environment : Environment} {index : Nat} {value : Value}
    (found : lookup environment index = some value) : (index, value) ∈ environment := by
  unfold lookup at found
  cases search : environment.find? (fun binding => binding.1 == index) with
  | none => simp [search] at found
  | some binding =>
    simp only [search, Option.map_some, Option.some.injEq] at found
    have member := List.mem_of_find?_eq_some search
    have key := List.find?_some search
    rcases binding with ⟨first, second⟩
    simp only [beq_iff_eq] at key found
    subst key
    subst found
    exact member

theorem forall₂_instantiates {bound : Environment} :
    ∀ {heads : List Head} {found : List Occ},
      List.Forall₂ (fun head occurrence => instantiateTerms bound head.arguments = some occurrence.values) heads found →
      ∀ head ∈ heads, ∃ values, instantiateTerms bound head.arguments = some values
  | [], [], .nil => by simp
  | _ :: _, _ :: _, .cons first rest => by
    intro head member
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨_, first⟩
    · exact forall₂_instantiates rest head later

theorem forall₂_append {α β : Type} {relation : α → β → Prop} :
    ∀ {first : List α} {second : List β} {third : List α} {fourth : List β},
      List.Forall₂ relation first second → List.Forall₂ relation third fourth →
      List.Forall₂ relation (first ++ third) (second ++ fourth)
  | [], [], _, _, .nil, later => later
  | _ :: _, _ :: _, _, _, .cons head rest, later => .cons head (forall₂_append rest later)

theorem forall₂_length {α β : Type} {relation : α → β → Prop} :
    ∀ {first : List α} {second : List β}, List.Forall₂ relation first second → first.length = second.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ rest => by simp [forall₂_length rest]

theorem ids_picksOf : ∀ (heads : List Head) (occurrences : List Occurrence), heads.length = occurrences.length →
    ids (picksOf heads occurrences) = occurrences.map Occurrence.id
  | [], [], _ => rfl
  | head :: heads, occurrence :: occurrences, same => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at same
    simp [picksOf, ids, ← ids_picksOf heads occurrences same] at *
  | [], _ :: _, same => by simp at same
  | _ :: _, [], same => by simp at same

theorem located_of_active {occurrences : List Occurrence} (distinct : (occurrences.map Occurrence.id).Nodup)
    {position active : Nat} (activeAt : ∃ occurrence, occurrences[position]? = some occurrence ∧ occurrence.id = active) :
    ∀ (offset : Nat) (occurrence : Occurrence), occurrences[offset]? = some occurrence →
      (0 + offset = position ↔ occurrence.id = active) := by
  intro offset occurrence found
  obtain ⟨activeOccurrence, atPosition, isActive⟩ := activeAt
  rw [Nat.zero_add]
  constructor
  · rintro rfl
    rw [atPosition, Option.some.injEq] at found
    subst found
    exact isActive
  · intro same
    have mapped : (occurrences.map Occurrence.id)[offset]? = (occurrences.map Occurrence.id)[position]? := by
      simp [found, atPosition, same, isActive]
    have offsetBound : offset < (occurrences.map Occurrence.id).length := by
      simpa using (List.getElem?_eq_some_iff.mp found).1
    have positionBound : position < (occurrences.map Occurrence.id).length := by
      simpa using (List.getElem?_eq_some_iff.mp atPosition).1
    rw [List.getElem?_eq_getElem offsetBound, List.getElem?_eq_getElem positionBound, Option.some.injEq] at mapped
    exact (List.Nodup.getElem_inj_iff distinct).mp mapped

theorem exhausted_unusable (store : Store) (coherent : Coherent store) (occurrence : At)
    (history : List CHR.Key) (active : Nat) (values : List Value)
    (activeStored : ∀ stored ∈ contents store, stored.id = active → stored.constraint.arguments = values)
    (rejectedAll : ∀ selection ∈ selections store occurrence.head active values 0 occurrence.body.heads [] [] [],
      Stale occurrence history selection ∨ guardsEval selection.1 occurrence.body.guards = .ok false)
    (operational : List Occurrence) (permuted : operational.Perm (contents store))
    (environment : Environment) (selection : Selection)
    (matched : selection.Matches occurrence.body environment operational)
    (activeAt : selection.ActiveAt active occurrence.head) :
    ¬ selection.Fresh occurrence.body occurrence.rule history ∨
      guardsEval environment occurrence.body.guards = .ok false := by
  obtain ⟨split, distinct, keptMatch, removedMatch, keysDistinct, onlyRule⟩ := matched
  have instantiated : List.Forall₂ (fun head stored => head.instantiate environment = some stored.constraint)
      occurrence.body.heads selection.heads := forall₂_append keptMatch removedMatch
  have stored : ∀ chosen ∈ selection.heads, chosen ∈ contents store := by
    intro chosen member
    apply permuted.subset
    apply split.symm.subset
    simp only [Selection.heads, List.mem_append] at member ⊢
    rcases member with kept | removed
    · exact .inl (.inl kept)
    · exact .inl (.inr removed)
  have fitting := allFit_intro store occurrence.head active values environment 0 occurrence.body.heads
    selection.heads instantiated stored (located_of_active distinct activeAt)
    (fun chosen member same => activeStored chosen (stored chosen member) same) coherent
  obtain ⟨bound, reached, grown⟩ := selections_complete store occurrence.head active values environment 0
    occurrence.body.heads selection.heads [] [] [] instantiated fitting distinct (by simp)
    (fun index value inside => by simp [lookup] at inside)
  have rejected := rejectedAll _ reached
  have lengths := forall₂_length instantiated
  have sameIds : ids ([] ++ picksOf occurrence.body.heads selection.heads) = selection.heads.map Occurrence.id := by
    simpa using ids_picksOf occurrence.body.heads selection.heads lengths
  rcases rejected with stale | guarded
  · left
    intro fresh
    obtain ⟨propagating, recorded⟩ := stale
    simp only at recorded
    rw [sameIds] at recorded
    have empty : occurrence.body.removed = [] := by
      simpa [Rule.propagation] using propagating
    exact fresh empty recorded
  · right
    have reachedFacts := selections_sound store occurrence.head active values 0 occurrence.body.heads [] [] []
      bound _ reached
    obtain ⟨found, _, instantiatedFound, _, _, _⟩ := reachedFacts.occurrences
    have agree : Agree bound environment := by
      intro index
      cases inBound : lookup bound index with
      | some value => exact (grown index value inBound).symm
      | none =>
        cases inEnvironment : lookup environment index with
        | none => rfl
        | some value =>
          exfalso
          have inRule := onlyRule (index, value) (mem_of_lookup inEnvironment)
          simp only [Rule.variables, List.mem_flatMap] at inRule
          obtain ⟨head, headMember, inHead⟩ := inRule
          obtain ⟨arguments, instantiatedHead⟩ := forall₂_instantiates instantiatedFound head headMember
          have isBound := instantiateTerms_bound head.arguments arguments instantiatedHead index
            (by simpa [Head.variables] using inHead)
          rw [inBound] at isBound
          simp at isBound
    simpa [guardsEval_agree agree] using guarded

#print axioms exhausted_unusable

end Mettapedia.Languages.CHR.Machine
