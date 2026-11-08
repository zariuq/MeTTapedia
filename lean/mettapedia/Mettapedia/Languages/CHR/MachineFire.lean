import Mettapedia.Languages.CHR.MachineSkip
import Mathlib.Data.List.Forall2

/-! A selection the machine reaches is an operational selection. Its picks
become the kept and removed head occurrences, the rest of the store contents
the unselected frame; the reached environment matches the rule over the
store contents, with the active constraint at its head position. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

/-- With distinct identifiers, a list is a permutation of chosen members
followed by its other elements. -/
theorem perm_chosen_rest {whole chosen : List Occurrence} (distinct : (whole.map Occurrence.id).Nodup)
    (chosenDistinct : (chosen.map Occurrence.id).Nodup) (subset : ∀ member ∈ chosen, member ∈ whole) :
    whole.Perm (chosen ++ whole.filter fun member => member.id ∉ chosen.map Occurrence.id) := by
  have wholeNodup := List.Nodup.of_map _ distinct
  have chosenNodup := List.Nodup.of_map _ chosenDistinct
  have appendNodup : (chosen ++ whole.filter fun member => member.id ∉ chosen.map Occurrence.id).Nodup := by
    rw [List.nodup_append]
    refine ⟨chosenNodup, wholeNodup.filter _, ?_⟩
    intro first inChosen second inRest same
    subst same
    simp only [List.mem_filter, decide_eq_true_eq] at inRest
    exact inRest.2 (List.mem_map_of_mem inChosen)
  apply (List.perm_ext_iff_of_nodup wholeNodup appendNodup).mpr
  intro member
  simp only [List.mem_append, List.mem_filter, decide_eq_true_eq]
  constructor
  · intro inWhole
    by_cases picked : member.id ∈ chosen.map Occurrence.id
    · obtain ⟨other, inChosen, same⟩ := List.mem_map.mp picked
      have equal := List.inj_on_of_nodup_map distinct (subset other inChosen) inWhole same
      exact .inl (equal ▸ inChosen)
    · exact .inr ⟨inWhole, picked⟩
  · rintro (inChosen | ⟨inWhole, _⟩)
    · exact subset member inChosen
    · exact inWhole

def leanOccurrences (heads : List Head) (found : List Occ) : List Occurrence :=
  List.zipWith (fun head occurrence => ⟨occurrence.id, ⟨head.name, occurrence.values⟩⟩) heads found

def selectionOf (rule : Rule) (store : Store) (found : List Occ) : Selection :=
  let chosen := leanOccurrences rule.heads found
  ⟨chosen.take rule.kept.length, chosen.drop rule.kept.length,
    (contents store).filter fun member => member.id ∉ chosen.map Occurrence.id⟩

theorem allFit_at (store : Store) (position active : Nat) (values : List Value) :
    ∀ (index : Nat) (heads : List Head) (occurrences : List Occurrence),
      AllFit store position active values index heads occurrences →
      ∀ (offset : Nat) (head : Head) (occurrence : Occurrence),
        heads[offset]? = some head → occurrences[offset]? = some occurrence →
        Fits store position active values (index + offset) head occurrence
  | _, [], [], _, offset, head, _, found, _ => by simp at found
  | index, first :: heads, occurrence :: occurrences, ⟨fits, rest⟩, offset, head, chosen, atHead, atOccurrence => by
    cases offset with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at atHead atOccurrence
      subst atHead
      subst atOccurrence
      simpa using fits
    | succ offset =>
      simp only [List.getElem?_cons_succ] at atHead atOccurrence
      have later := allFit_at store position active values (index + 1) heads occurrences rest offset head chosen
        atHead atOccurrence
      rwa [show index + 1 + offset = index + (offset + 1) by omega] at later
  | _, [], _ :: _, fitting, _, _, _, _, _ => by simp [AllFit] at fitting
  | _, _ :: _, [], fitting, _, _, _, _, _ => by simp [AllFit] at fitting

theorem leanOccurrences_ids : ∀ (heads : List Head) (found : List Occ), heads.length = found.length →
    (leanOccurrences heads found).map Occurrence.id = found.map Occ.id
  | [], [], _ => rfl
  | _ :: heads, _ :: found, same => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at same
    simp [leanOccurrences, ← leanOccurrences_ids heads found same]
  | [], _ :: _, same => by simp at same
  | _ :: _, [], same => by simp at same

theorem forall₂_lean {bound : Environment} : ∀ {heads : List Head} {found : List Occ},
    List.Forall₂ (fun head occurrence => instantiateTerms bound head.arguments = some occurrence.values) heads found →
    List.Forall₂ (fun head occurrence => head.instantiate bound = some occurrence.constraint)
      heads (leanOccurrences heads found)
  | [], [], .nil => .nil
  | head :: _, occurrence :: _, .cons first rest => by
    refine .cons ?_ (forall₂_lean rest)
    unfold Head.instantiate
    rw [← instantiateTerms_eq, first]
    rfl

theorem ids_zipWith : ∀ (heads : List Head) (found : List Occ), heads.length = found.length →
    ids (List.zipWith (fun head occurrence => (⟨Head.key head, occurrence.id⟩ : Pick)) heads found) =
      found.map Occ.id
  | [], [], _ => rfl
  | _ :: heads, _ :: found, same => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at same
    simp [ids, ← ids_zipWith heads found same]
  | [], _ :: _, same => by simp at same
  | _ :: _, [], same => by simp at same

/-- The stored occurrences behind a reached selection: one per head, with
distinct identifiers and the heads' arities. -/
structure Found (store : Store) (heads : List Head) (chosen : List Pick) (found : List Occ) : Prop where
  picks : chosen = List.zipWith (fun head occurrence => (⟨Head.key head, occurrence.id⟩ : Pick)) heads found
  lengths : heads.length = found.length
  distinct : (found.map Occ.id).Nodup
  stored : ∀ member ∈ leanOccurrences heads found, member ∈ contents store
  arities : List.Forall₂ (fun head occurrence => occurrence.values.length = head.arguments.length) heads found

theorem forall₂_arities {bound : Environment} : ∀ {heads : List Head} {found : List Occ},
    List.Forall₂ (fun head occurrence => instantiateTerms bound head.arguments = some occurrence.values) heads found →
    List.Forall₂ (fun head occurrence => occurrence.values.length = head.arguments.length) heads found
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons first rest =>
    .cons (mapM_length (by rw [← instantiateTerms_eq]; exact first)) (forall₂_arities rest)

theorem reached_matches (store : Store) (coherent : Coherent store) (occurrence : At)
    (active : Nat) (values : List Value)
    (activeStored : ∀ head, occurrence.body.heads[occurrence.head]? = some head →
      (⟨active, ⟨head.name, values⟩⟩ : Occurrence) ∈ contents store)
    (positionValid : ∃ head, occurrence.body.heads[occurrence.head]? = some head)
    {bound : Environment} {chosen : List Pick}
    (reached : (bound, chosen) ∈
      selections store occurrence.head active values 0 occurrence.body.heads [] [] []) :
    ∃ found : List Occ, Found store occurrence.body.heads chosen found ∧ ids chosen = found.map Occ.id ∧
      (selectionOf occurrence.body store found).Matches occurrence.body bound (contents store) ∧
      (selectionOf occurrence.body store found).ActiveAt active occurrence.head := by
  have facts := selections_sound store occurrence.head active values 0 occurrence.body.heads [] [] []
    bound chosen reached
  obtain ⟨found, chosenEq, instantiated, fitting, distinct, _⟩ := facts.occurrences
  have lengths := forall₂_length instantiated
  have chosenIds : (leanOccurrences occurrence.body.heads found).map Occurrence.id = found.map Occ.id :=
    leanOccurrences_ids occurrence.body.heads found lengths
  have stored : ∀ member ∈ leanOccurrences occurrence.body.heads found, member ∈ contents store := by
    intro member inside
    obtain ⟨offset, atOffset⟩ := List.mem_iff_getElem?.mp inside
    simp only [leanOccurrences, List.getElem?_zipWith] at atOffset
    cases headAt : occurrence.body.heads[offset]? with
    | none => simp [headAt] at atOffset
    | some head =>
      cases foundAt : found[offset]? with
      | none => simp [headAt, foundAt] at atOffset
      | some picked =>
        simp only [headAt, foundAt] at atOffset
        simp only [Option.some.injEq] at atOffset
        subst atOffset
        have fits := allFit_at store occurrence.head active values 0 occurrence.body.heads
          (leanOccurrences occurrence.body.heads found) fitting offset head
          ⟨picked.id, ⟨head.name, picked.values⟩⟩ headAt
          (by simp [leanOccurrences, List.getElem?_zipWith, headAt, foundAt])
        unfold Fits at fits
        rw [Nat.zero_add] at fits
        by_cases here : offset = occurrence.head
        · simp only [here, if_true] at fits
          obtain ⟨isActive, sameValues⟩ := fits
          subst here
          have inContents := activeStored head headAt
          rw [← isActive, ← sameValues] at inContents
          exact inContents
        · simp only [here, if_false] at fits
          have inContents := member_of_slot fits.1
          simpa [Head.key] using inContents
  have selectionHeads : (selectionOf occurrence.body store found).heads = leanOccurrences occurrence.body.heads found := by
    simp [selectionOf, Selection.heads]
  have leanForall := forall₂_lean instantiated
  refine ⟨found, ⟨by simpa using chosenEq, lengths, distinct, stored, forall₂_arities instantiated⟩,
    by rw [chosenEq]; simpa using ids_zipWith occurrence.body.heads found lengths, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have permuted := perm_chosen_rest coherent.ids (chosenIds ▸ distinct) stored
    simpa [selectionOf, List.take_append_drop] using permuted
  · rw [selectionHeads, chosenIds]
    exact distinct
  · have kept := List.forall₂_take occurrence.body.kept.length leanForall
    simpa [selectionOf, Rule.heads, List.take_left'] using kept
  · have removed := List.forall₂_drop occurrence.body.kept.length leanForall
    simpa [selectionOf, Rule.heads, List.drop_left'] using removed
  · exact facts.bindings.distinct List.nodup_nil
  · intro binding member
    rcases facts.bindings.only binding member with impossible | inHeads
    · cases impossible
    · simpa [Rule.variables] using inHeads
  · obtain ⟨head, headAt⟩ := positionValid
    have positionBound : occurrence.head < found.length := by
      rw [← lengths]
      exact (List.getElem?_eq_some_iff.mp headAt).1
    let picked := found[occurrence.head]
    have fits := allFit_at store occurrence.head active values 0 occurrence.body.heads
      (leanOccurrences occurrence.body.heads found) fitting occurrence.head head
      ⟨picked.id, ⟨head.name, picked.values⟩⟩ headAt
      (by simp [leanOccurrences, List.getElem?_zipWith, headAt, picked, List.getElem?_eq_getElem positionBound])
    unfold Fits at fits
    simp only [Nat.zero_add, if_true] at fits
    refine ⟨⟨picked.id, ⟨head.name, picked.values⟩⟩, ?_, fits.1⟩
    rw [selectionHeads]
    simp [leanOccurrences, List.getElem?_zipWith, headAt, picked, List.getElem?_eq_getElem positionBound]

#print axioms reached_matches

#print axioms perm_chosen_rest
#print axioms allFit_at
#print axioms forall₂_lean

end Mettapedia.Languages.CHR.Machine
