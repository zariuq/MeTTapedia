import Mettapedia.Languages.CHR.MachineStoreUpdate

/-! Removing picks. In a coherent store whose picks name the keys of the
occurrences they pick, removing the picks leaves exactly the occurrences
whose identifiers were not picked, and the store stays coherent. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

/-- The key under which an operational occurrence is stored. -/
def keyOf (occurrence : Occurrence) : Key := (occurrence.constraint.name, occurrence.constraint.arguments.length)

theorem mem_without {occurrences : List Occ} (distinct : (occurrences.map Occ.id).Nodup) (id : Nat) (member : Occ) :
    member ∈ without id occurrences ↔ member ∈ occurrences ∧ member.id ≠ id := by
  induction occurrences with
  | nil => simp [without]
  | cons first rest ih =>
    rw [List.map_cons, List.nodup_cons] at distinct
    unfold without
    by_cases hit : first.id = id
    · simp only [hit, if_true, List.mem_cons]
      constructor
      · intro inRest
        refine ⟨.inr inRest, fun same => distinct.1 ?_⟩
        rw [hit, ← same]
        exact List.mem_map_of_mem inRest
      · rintro ⟨rfl | inRest, different⟩
        · exact absurd hit different
        · exact inRest
    · simp only [hit, if_false, List.mem_cons, ih distinct.2]
      constructor
      · rintro (rfl | ⟨inRest, different⟩)
        · exact ⟨.inl rfl, hit⟩
        · exact ⟨.inr inRest, different⟩
      · rintro ⟨rfl | inRest, different⟩
        · exact .inl rfl
        · exact .inr ⟨inRest, different⟩

theorem mem_lift {key : Key} {occurrences : List Occ} {member : Occurrence} :
    member ∈ occurrences.map (lift key) ↔ ∃ stored ∈ occurrences, lift key stored = member := by
  simp [List.mem_map]

theorem contents_ids_nodup_slot {store : Store} (coherent : Coherent store) (key : Key) :
    ((slot key store).map Occ.id).Nodup := by
  have split := contents_split key store coherent.keys
  have ids := (split.map Occurrence.id).nodup_iff.mp coherent.ids
  rw [List.map_append] at ids
  have slotIds := (List.nodup_append.mp ids).2.1
  simpa [List.map_map, lift, Function.comp_def] using slotIds

/-- Picks name the keys of the occurrences they pick. -/
def Keyed (store : Store) (picks : List Pick) : Prop :=
  ∀ pick ∈ picks, ∀ member ∈ contents store, member.id = pick.id → keyOf member = pick.key

theorem keyOf_lift {store : Store} (coherent : Coherent store) {entry : Key × List Occ} (inStore : entry ∈ store)
    {stored : Occ} (inSlot : stored ∈ entry.2) : keyOf (lift entry.1 stored) = entry.1 := by
  have arity := coherent.arity entry inStore stored inSlot
  simp [keyOf, lift, arity]

theorem mem_contents_iff {store : Store} {member : Occurrence} :
    member ∈ contents store ↔ ∃ entry ∈ store, ∃ stored ∈ entry.2, lift entry.1 stored = member := by
  simp [contents, lift, List.mem_flatMap, List.mem_map]

/-- Removing one pick from its slot removes exactly the occurrence with its
identifier. -/
theorem contents_remove_one {store : Store} (coherent : Coherent store) (pick : Pick)
    (keyed : ∀ member ∈ contents store, member.id = pick.id → keyOf member = pick.key) (member : Occurrence) :
    member ∈ contents (put pick.key (without pick.id (slot pick.key store)) store) ↔
      member ∈ contents store ∧ member.id ≠ pick.id := by
  have afterPut := contents_put pick.key (without pick.id (slot pick.key store)) store coherent.keys
  have before := contents_split pick.key store coherent.keys
  rw [afterPut.mem_iff, before.mem_iff, List.mem_append, List.mem_append]
  have slotDistinct := contents_ids_nodup_slot coherent pick.key
  constructor
  · rintro (erased | inWithout)
    · refine ⟨.inl erased, fun same => ?_⟩
      have inContents : member ∈ contents store := before.mem_iff.mpr (List.mem_append_left _ erased)
      have keyEq := keyed member inContents same
      obtain ⟨entry, inErased, stored, inSlot, rfl⟩ := mem_contents_iff.mp erased
      simp only [eraseKey, List.mem_filter, decide_eq_true_eq] at inErased
      have keyOfEq := keyOf_lift coherent inErased.1 inSlot
      exact inErased.2 (keyOfEq ▸ keyEq)
    · obtain ⟨stored, inStored, rfl⟩ := mem_lift.mp inWithout
      have facts := (mem_without slotDistinct pick.id stored).mp inStored
      exact ⟨.inr (List.mem_map_of_mem facts.1), by simpa [lift] using facts.2⟩
  · rintro ⟨erased | inSlotLift, different⟩
    · exact .inl erased
    · obtain ⟨stored, inStored, rfl⟩ := mem_lift.mp inSlotLift
      exact .inr (List.mem_map_of_mem ((mem_without slotDistinct pick.id stored).mpr ⟨inStored, by simpa [lift] using different⟩))

theorem without_sublist (id : Nat) : ∀ (occurrences : List Occ), List.Sublist (without id occurrences) occurrences
  | [] => .slnil
  | first :: rest => by
    unfold without
    by_cases hit : first.id = id
    · simp only [hit, if_true]
      exact List.sublist_cons_self first rest
    · simp only [hit, if_false]
      exact (without_sublist id rest).cons_cons first

theorem mem_put {key : Key} {occurrences : List Occ} :
    ∀ {store : Store} {entry : Key × List Occ}, entry ∈ put key occurrences store →
      entry ∈ store ∨ entry = (key, occurrences)
  | [], entry, member => by simp [put] at member; exact .inr member
  | (other, old) :: rest, entry, member => by
    unfold put at member
    by_cases same : other = key
    · simp only [same, if_true, List.mem_cons] at member
      rcases member with rfl | later
      · exact .inr rfl
      · exact .inl (List.mem_cons_of_mem _ later)
    · simp only [same, if_false, List.mem_cons] at member
      rcases member with rfl | later
      · exact .inl List.mem_cons_self
      · rcases mem_put later with old' | fresh
        · exact .inl (List.mem_cons_of_mem _ old')
        · exact .inr fresh

theorem slot_arity {store : Store} (coherent : Coherent store) (key : Key) :
    ∀ stored ∈ slot key store, stored.values.length = key.2 := by
  intro stored inSlot
  induction store with
  | nil => cases inSlot
  | cons first rest ih =>
    rcases first with ⟨other, others⟩
    unfold slot at inSlot
    by_cases same : other = key
    · subst same
      simp only [if_true] at inSlot
      exact coherent.arity _ List.mem_cons_self stored inSlot
    · simp only [same, if_false] at inSlot
      have restCoherent : Coherent rest := ⟨(List.nodup_cons.mp (by simpa using coherent.keys)).2,
        fun entry member => coherent.arity entry (List.mem_cons_of_mem _ member),
        by
          have ids := coherent.ids
          rw [contents_cons, List.map_append] at ids
          exact (List.nodup_append.mp ids).2.1⟩
      exact ih restCoherent inSlot

/-- Removing one pick keeps the store coherent. -/
theorem coherent_remove_one {store : Store} (coherent : Coherent store) (pick : Pick) :
    Coherent (put pick.key (without pick.id (slot pick.key store)) store) where
  keys := put_keys _ _ store coherent.keys
  arity := by
    intro entry member stored inSlot
    rcases mem_put member with old | fresh
    · exact coherent.arity entry old stored inSlot
    · subst fresh
      exact slot_arity coherent pick.key stored ((without_sublist pick.id _).subset inSlot)
  ids := by
    have afterPut := contents_put pick.key (without pick.id (slot pick.key store)) store coherent.keys
    have before := contents_split pick.key store coherent.keys
    have beforeIds := (before.map Occurrence.id).nodup_iff.mp coherent.ids
    have smaller : List.Sublist
        ((contents (eraseKey pick.key store) ++ (without pick.id (slot pick.key store)).map (lift pick.key)).map Occurrence.id)
        ((contents (eraseKey pick.key store) ++ (slot pick.key store).map (lift pick.key)).map Occurrence.id) :=
      (((without_sublist pick.id _).map (lift pick.key)).append_left _).map _
    exact (afterPut.map Occurrence.id).nodup_iff.mpr (smaller.nodup beforeIds)

#print axioms coherent_remove_one

theorem removePicks_spec : ∀ (picks : List Pick) (store : Store), Coherent store → Keyed store picks →
    Coherent (removePicks picks store) ∧
      ∀ member, member ∈ contents (removePicks picks store) ↔ member ∈ contents store ∧ member.id ∉ ids picks
  | [], store, coherent, _ => ⟨coherent, fun member => by simp [removePicks, ids]⟩
  | pick :: rest, store, coherent, keyed => by
    have nextCoherent := coherent_remove_one coherent pick
    have nextMem := contents_remove_one coherent pick (keyed pick List.mem_cons_self)
    have restKeyed : Keyed (put pick.key (without pick.id (slot pick.key store)) store) rest := by
      intro later inRest member inNext same
      exact keyed later (List.mem_cons_of_mem _ inRest) member ((nextMem member).mp inNext).1 same
    obtain ⟨finalCoherent, finalMem⟩ :=
      removePicks_spec rest (put pick.key (without pick.id (slot pick.key store)) store) nextCoherent restKeyed
    refine ⟨finalCoherent, fun member => ?_⟩
    show member ∈ contents (removePicks rest (put pick.key (without pick.id (slot pick.key store)) store)) ↔ _
    rw [finalMem, nextMem]
    simp only [ids, List.map_cons, List.mem_cons, not_or]
    constructor
    · rintro ⟨⟨inStore, different⟩, notRest⟩
      exact ⟨inStore, different, notRest⟩
    · rintro ⟨inStore, different, notRest⟩
      exact ⟨⟨inStore, different⟩, notRest⟩

#print axioms removePicks_spec

#print axioms contents_remove_one

end Mettapedia.Languages.CHR.Machine
