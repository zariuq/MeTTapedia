import Mettapedia.Languages.CHR.MachineFire

/-! Store updates and the operational contents. Up to permutation, a store's
contents are the other keys' contents followed by one key's slot, and `put`
replaces exactly that slot. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

def lift (key : Key) (occurrence : Occ) : Occurrence := ⟨occurrence.id, ⟨key.1, occurrence.values⟩⟩

/-- The store without the slot of `key`. -/
def eraseKey (key : Key) (store : Store) : Store := store.filter fun entry => entry.1 ≠ key

theorem contents_cons (key : Key) (occurrences : List Occ) (rest : Store) :
    contents ((key, occurrences) :: rest) = occurrences.map (lift key) ++ contents rest := by
  simp [contents, lift]

theorem slot_absent {store : Store} {key : Key} (absent : key ∉ store.map Prod.fst) : slot key store = [] := by
  induction store with
  | nil => rfl
  | cons first rest ih =>
    rcases first with ⟨other, others⟩
    have different : other ≠ key := fun same => absent (by simp [same])
    simp only [slot, different, if_false]
    exact ih (fun inside => absent (by simp [inside]))

theorem eraseKey_absent {store : Store} {key : Key} (absent : key ∉ store.map Prod.fst) :
    eraseKey key store = store := by
  unfold eraseKey
  apply List.filter_eq_self.mpr
  intro entry member
  have different : entry.1 ≠ key := fun same => absent (same ▸ List.mem_map_of_mem member)
  simpa using different

/-- A store's contents split around one key. -/
theorem contents_split (key : Key) :
    ∀ (store : Store), (store.map Prod.fst).Nodup →
      (contents store).Perm (contents (eraseKey key store) ++ (slot key store).map (lift key))
  | [], _ => by simp [contents, eraseKey, slot]
  | (other, old) :: rest, keys => by
    rw [List.map_cons, List.nodup_cons] at keys
    by_cases same : other = key
    · subst same
      have restErased : eraseKey other rest = rest := eraseKey_absent keys.1
      simp only [contents_cons, eraseKey, slot, if_true, ne_eq, not_true_eq_false, decide_false,
        List.filter_cons_of_neg, Bool.false_eq_true, not_false_eq_true]
      rw [show List.filter (fun entry => decide ¬entry.1 = other) rest = eraseKey other rest from rfl, restErased]
      exact List.perm_append_comm
    · have inner := contents_split key rest keys.2
      simp only [contents_cons, eraseKey, slot, same, if_false, ne_eq, not_false_eq_true, decide_true,
        List.filter_cons_of_pos]
      rw [show List.filter (fun entry => decide ¬entry.1 = key) rest = eraseKey key rest from rfl]
      rw [List.append_assoc]
      exact inner.append_left _

/-- `put` replaces exactly the slot of its key. -/
theorem contents_put (key : Key) (occurrences : List Occ) :
    ∀ (store : Store), (store.map Prod.fst).Nodup →
      (contents (put key occurrences store)).Perm (contents (eraseKey key store) ++ occurrences.map (lift key))
  | [], _ => by
    rw [put, contents_cons]
    simp [contents, eraseKey]
  | (other, old) :: rest, keys => by
    rw [List.map_cons, List.nodup_cons] at keys
    by_cases same : other = key
    · subst same
      have restErased : eraseKey other rest = rest := eraseKey_absent keys.1
      simp only [put, if_true, contents_cons, eraseKey, ne_eq, not_true_eq_false, decide_false,
        List.filter_cons_of_neg, Bool.false_eq_true, not_false_eq_true]
      rw [show List.filter (fun entry => decide ¬entry.1 = other) rest = eraseKey other rest from rfl, restErased]
      exact List.perm_append_comm
    · have inner := contents_put key occurrences rest keys.2
      simp only [put, same, if_false, contents_cons, eraseKey, ne_eq, not_false_eq_true, decide_true,
        List.filter_cons_of_pos]
      rw [show List.filter (fun entry => decide ¬entry.1 = key) rest = eraseKey key rest from rfl]
      rw [List.append_assoc]
      exact inner.append_left _

theorem put_keys (key : Key) (occurrences : List Occ) :
    ∀ (store : Store), (store.map Prod.fst).Nodup → ((put key occurrences store).map Prod.fst).Nodup
  | [], _ => by simp [put]
  | (other, old) :: rest, keys => by
    rw [List.map_cons, List.nodup_cons] at keys
    by_cases same : other = key
    · subst same
      simpa [put] using keys
    · simp only [put, same, if_false, List.map_cons, List.nodup_cons]
      refine ⟨?_, put_keys key occurrences rest keys.2⟩
      intro inside
      have inPut : ∀ (store : Store), other ∉ store.map Prod.fst → other ≠ key →
          other ∉ (put key occurrences store).map Prod.fst := by
        intro store
        induction store with
        | nil => intro _ different; simpa [put] using different
        | cons entry more ih =>
          intro absent different
          rcases entry with ⟨k, v⟩
          by_cases hit : k = key
          · subst hit; simpa [put] using absent
          · simp only [put, hit, if_false, List.map_cons, List.mem_cons, not_or]
            simp only [List.map_cons, List.mem_cons, not_or] at absent
            exact ⟨absent.1, ih absent.2 different⟩
      exact inPut rest keys.1 same inside

#print axioms contents_split
#print axioms contents_put
#print axioms put_keys

end Mettapedia.Languages.CHR.Machine
