import Mettapedia.Languages.CHR.MachineRemove

/-! The store after a firing. Removing the removed picks of a reached
selection leaves a coherent store whose contents are the operational
commit's store: the kept head occurrences followed by the unselected frame. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

def chosenPicks (heads : List Head) (found : List Occ) : List Pick :=
  List.zipWith (fun head occurrence => ⟨Head.key head, occurrence.id⟩) heads found

theorem mem_chosenPicks {heads : List Head} {found : List Occ} {pick : Pick}
    (member : pick ∈ chosenPicks heads found) :
    ∃ (offset : Nat) (head : Head) (occurrence : Occ), heads[offset]? = some head ∧
      found[offset]? = some occurrence ∧ pick = ⟨Head.key head, occurrence.id⟩ := by
  obtain ⟨offset, atOffset⟩ := List.mem_iff_getElem?.mp member
  simp only [chosenPicks, List.getElem?_zipWith] at atOffset
  cases headAt : heads[offset]? with
  | none => simp [headAt] at atOffset
  | some head =>
    cases foundAt : found[offset]? with
    | none => simp [headAt, foundAt] at atOffset
    | some occurrence =>
      simp only [headAt, foundAt, Option.some.injEq] at atOffset
      exact ⟨offset, head, occurrence, headAt, foundAt, atOffset.symm⟩

theorem keyed_chosen (store : Store) (coherent : Coherent store) (heads : List Head) (found : List Occ)
    (stored : ∀ member ∈ leanOccurrences heads found, member ∈ contents store)
    (arities : List.Forall₂ (fun head occurrence => occurrence.values.length = head.arguments.length) heads found)
    (picks : List Pick) (subset : ∀ pick ∈ picks, pick ∈ chosenPicks heads found) :
    Keyed store picks := by
  intro pick inPicks member inContents same
  obtain ⟨offset, head, occurrence, headAt, foundAt, rfl⟩ := mem_chosenPicks (subset pick inPicks)
  have chosen : (⟨occurrence.id, ⟨head.name, occurrence.values⟩⟩ : Occurrence) ∈ leanOccurrences heads found := by
    apply List.mem_iff_getElem?.mpr
    exact ⟨offset, by simp [leanOccurrences, List.getElem?_zipWith, headAt, foundAt]⟩
  have equal := contents_unique coherent inContents (stored _ chosen) same
  subst equal
  have arity : occurrence.values.length = head.arguments.length := by
    have aligned := List.forall₂_iff_get.mp arities
    have offsetHeads : offset < heads.length := (List.getElem?_eq_some_iff.mp headAt).1
    have offsetFound : offset < found.length := (List.getElem?_eq_some_iff.mp foundAt).1
    have atHead := (List.getElem?_eq_some_iff.mp headAt).2
    have atFound := (List.getElem?_eq_some_iff.mp foundAt).2
    have pointwise := aligned.2 offset offsetHeads offsetFound
    simp only [List.get_eq_getElem, atHead, atFound] at pointwise
    exact pointwise
  simp [keyOf, Head.key, arity]

theorem commit_store (store : Store) (coherent : Coherent store) (rule : Rule) (found : List Occ)
    (lengths : rule.heads.length = found.length) (distinct : (found.map Occ.id).Nodup)
    (stored : ∀ member ∈ leanOccurrences rule.heads found, member ∈ contents store)
    (arities : List.Forall₂ (fun head occurrence => occurrence.values.length = head.arguments.length)
      rule.heads found) :
    Coherent (removePicks ((chosenPicks rule.heads found).drop rule.kept.length) store) ∧
      (contents (removePicks ((chosenPicks rule.heads found).drop rule.kept.length) store)).Perm
        ((selectionOf rule store found).kept ++ (selectionOf rule store found).rest) := by
  have keyed := keyed_chosen store coherent rule.heads found stored arities
    ((chosenPicks rule.heads found).drop rule.kept.length) (fun pick member => List.mem_of_mem_drop member)
  obtain ⟨finalCoherent, finalMem⟩ := removePicks_spec _ store coherent keyed
  refine ⟨finalCoherent, ?_⟩
  have chosenIds : (leanOccurrences rule.heads found).map Occurrence.id = found.map Occ.id :=
    leanOccurrences_ids rule.heads found lengths
  have picksIds : ids (chosenPicks rule.heads found) = found.map Occ.id := ids_zipWith rule.heads found lengths
  let chosen := leanOccurrences rule.heads found
  have removedIds : ids ((chosenPicks rule.heads found).drop rule.kept.length) =
      (chosen.drop rule.kept.length).map Occurrence.id := by
    have picked : (chosenPicks rule.heads found).map Pick.id = found.map Occ.id := picksIds
    simp only [ids, List.map_drop, picked]
    show List.drop rule.kept.length (found.map Occ.id) =
      List.drop rule.kept.length ((leanOccurrences rule.heads found).map Occurrence.id)
    rw [chosenIds]
  have chosenDistinct : (chosen.map Occurrence.id).Nodup := chosenIds ▸ distinct
  have contentsNodup : (contents (removePicks ((chosenPicks rule.heads found).drop rule.kept.length) store)).Nodup :=
    List.Nodup.of_map _ finalCoherent.ids
  have split : chosen = chosen.take rule.kept.length ++ chosen.drop rule.kept.length := (List.take_append_drop _ _).symm
  have splitIds := chosenDistinct
  rw [split, List.map_append] at splitIds
  have disjoint := (List.nodup_append.mp splitIds).2.2
  have keptNodup : (chosen.take rule.kept.length).Nodup :=
    List.Nodup.of_map Occurrence.id (List.nodup_append.mp splitIds).1
  have targetNodup : ((selectionOf rule store found).kept ++ (selectionOf rule store found).rest).Nodup := by
    simp only [selectionOf]
    rw [List.nodup_append]
    refine ⟨keptNodup, (List.Nodup.of_map _ coherent.ids).filter _, ?_⟩
    intro first inKept second inRest same
    subst same
    simp only [List.mem_filter, decide_eq_true_eq] at inRest
    exact inRest.2 (List.mem_map_of_mem (List.mem_of_mem_take inKept))
  apply (List.perm_ext_iff_of_nodup contentsNodup targetNodup).mpr
  intro member
  rw [finalMem, removedIds]
  simp only [selectionOf, List.mem_append, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨inStore, notRemoved⟩
    by_cases picked : member.id ∈ chosen.map Occurrence.id
    · left
      obtain ⟨other, inChosen, sameId⟩ := List.mem_map.mp picked
      have equal := contents_unique coherent (stored other inChosen) inStore sameId
      subst equal
      rw [split] at inChosen
      rcases List.mem_append.mp inChosen with inKept | inRemoved
      · exact inKept
      · exact absurd (List.mem_map_of_mem inRemoved) notRemoved
    · exact .inr ⟨inStore, picked⟩
  · rintro (inKept | ⟨inStore, notChosen⟩)
    · refine ⟨stored member (List.mem_of_mem_take inKept), fun inRemoved => ?_⟩
      obtain ⟨other, inDrop, sameId⟩ := List.mem_map.mp inRemoved
      exact disjoint _ (List.mem_map_of_mem inKept) _ (List.mem_map_of_mem inDrop) sameId.symm
    · exact ⟨inStore, fun inRemoved => notChosen (by
        obtain ⟨other, inDrop, sameId⟩ := List.mem_map.mp inRemoved
        exact sameId ▸ List.mem_map_of_mem (List.mem_of_mem_drop inDrop))⟩

/-- Introducing a fresh occurrence adds exactly it and keeps the store coherent. -/
theorem introduce_store (store : Store) (coherent : Coherent store) (key : Key) (new : Occ)
    (fresh : new.id ∉ (contents store).map Occurrence.id) (arity : new.values.length = key.2) :
    Coherent (put key (new :: slot key store) store) ∧
      (contents (put key (new :: slot key store) store)).Perm (contents store ++ [lift key new]) := by
  have afterPut := contents_put key (new :: slot key store) store coherent.keys
  have before := contents_split key store coherent.keys
  have perm : (contents (put key (new :: slot key store) store)).Perm (contents store ++ [lift key new]) := by
    refine afterPut.trans ?_
    rw [List.map_cons]
    refine List.perm_middle.trans ?_
    exact (List.perm_cons _).mpr before.symm |>.trans (List.perm_append_singleton _ _).symm
  refine ⟨⟨put_keys _ _ store coherent.keys, ?_, ?_⟩, perm⟩
  · intro entry member stored inSlot
    rcases mem_put member with old | added
    · exact coherent.arity entry old stored inSlot
    · subst added
      rcases List.mem_cons.mp inSlot with rfl | inOld
      · exact arity
      · exact slot_arity coherent key stored inOld
  · apply (perm.map Occurrence.id).nodup_iff.mpr
    rw [List.map_append, List.nodup_append]
    refine ⟨coherent.ids, by simp, ?_⟩
    intro first inStore second inNew same
    simp only [List.map_cons, List.map_nil, List.mem_singleton, lift] at inNew
    subst inNew
    subst same
    exact fresh inStore

#print axioms introduce_store

#print axioms keyed_chosen
#print axioms commit_store

end Mettapedia.Languages.CHR.Machine
