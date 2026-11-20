import Mettapedia.Ownership.Step

/-!
# Every step preserves the separation invariant

`Valid` is a property of the loans, the allocations and the release
authorities alone. A step changes them in a few ways only: it adds a loan, adds
an allocation with its root loan, erases a loan that has ended, drops an owner
whose storage nothing uses, narrows a loan's region, or renames a loan. Each way
needs only a check on the objects it touches, never a check of every pair of
loans; the lemmas below say what each needs.
-/

set_option autoImplicit false

namespace Mettapedia.Ownership

open Mettapedia.Machines.CMemory.Borrowing

/-! ## Actions that touch no loan, allocation or authority -/

theorem metadata_preserves_valid {s after : State} {a : Action}
    (isMetadata : metadata a = true) (h : transition s a = some after)
    (valid : Valid s) : Valid after := by
  cases a <;> simp only [metadata] at isMetadata <;> try contradiction
  case access id region writing =>
    obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp h
    have equal := Option.some.inj same
    subst after
    refine (valid_congr (s := s) ?_ ?_ ?_).mp valid <;> rfl
  case view id region length writing =>
    obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp h
    cases Option.some.inj same
    refine (valid_congr (s := s) ?_ ?_ ?_).mp valid <;> rfl
  case result id region writing =>
    obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
    have equal := Option.some.inj same
    subst after
    refine (valid_congr (s := s) ?_ ?_ ?_).mp valid <;> rfl
  case nullResult =>
    obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp h
    have equal := Option.some.inj same
    subst after
    refine (valid_congr (s := s) ?_ ?_ ?_).mp valid <;> rfl
  case fieldResult key id region writing =>
    obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
    cases Option.some.inj same
    refine (valid_congr (s := s) ?_ ?_ ?_).mp valid <;> rfl
  case nullFieldResult key =>
    obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp h
    cases Option.some.inj same
    refine (valid_congr (s := s) ?_ ?_ ?_).mp valid <;> rfl
  case recordResult key id region writing =>
    obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
    cases Option.some.inj same
    refine (valid_congr (s := s) ?_ ?_ ?_).mp valid <;> rfl
  case nullRecordResult key =>
    obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
    cases Option.some.inj same
    refine (valid_congr (s := s) ?_ ?_ ?_).mp valid <;> rfl
  case invoke name arguments =>
    obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp h
    have equal := Option.some.inj same
    subst after
    refine (valid_congr (s := s) ?_ ?_ ?_).mp valid <;> rfl


/-! ## Erasing a loan that has ended -/

theorem mem_endLoan {loans : List Loan} {id : Nat} {l : Loan} :
    l ∈ endLoan loans id ↔ l ∈ loans ∧ l.id ≠ id := by
  simp [endLoan, List.mem_filter]

/-- A loan none of whose descendants is live can be erased. -/
theorem valid_erase {s : State} {id : Nat} (valid : Valid s) (ended : ∀ l ∈ s.loans, id ∉ l.ancestors) :
    Valid { s with loans := endLoan s.loans id } := by
  obtain ⟨ids, roots, authorityRoots, ordered, covered, parents, compatible, heap, holders⟩ := valid
  refine ⟨?_, roots, authorityRoots, ?_, ?_, ?_, ?_, heap, holders⟩
  · exact ids.sublist (List.filter_sublist.map _)
  · intro l present parent mem
    exact ordered l (mem_endLoan.mp present).1 parent mem
  · intro l present
    exact covered l (mem_endLoan.mp present).1
  · intro l present p parent
    obtain ⟨q, qPresent, rest⟩ := parents l (mem_endLoan.mp present).1 p parent
    refine ⟨q, mem_endLoan.mpr ⟨qPresent, ?_⟩, rest⟩
    intro same
    exact ended l (mem_endLoan.mp present).1 (by rw [← same, rest.1]; exact parent)
  · intro a aPresent b bPresent different
    exact compatible a (mem_endLoan.mp aPresent).1 b (mem_endLoan.mp bPresent).1 different

/-! ## Adding a loan -/

theorem compatible_symm {a b : Loan} (h : Compatible a b) : Compatible b a := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl (Region.disjoint_symm h)))
  · exact Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩))

/-- A new loan needs a fresh id, ancestors below it, storage that is allocated,
live ancestors that contain it and allow its mode, and compatibility with every
loan already present. -/
theorem valid_add_loan {s : State} {n : Loan} (valid : Valid s)
    (fresh : ∀ l ∈ s.loans, l.id ≠ n.id)
    (below : ∀ p ∈ n.ancestors, p < n.id)
    (allocated : ∃ a ∈ s.allocations, a.region.Contains n.region)
    (parents : ∀ id ∈ n.ancestors, ∃ p ∈ s.loans,
      p.id = id ∧ p.region.Contains n.region ∧ (p.mode = .shared → n.mode = .shared))
    (compatible : ∀ l ∈ s.loans, Compatible n l) :
    Valid { s with loans := s.loans ++ [n] } := by
  obtain ⟨ids, roots, authorityRoots, ordered, covered, live, pairs, heap, holders⟩ := valid
  refine ⟨?_, roots, authorityRoots, ?_, ?_, ?_, ?_, heap, holders⟩
  · simp only [List.map_append, List.map_cons, List.map_nil]
    refine List.Nodup.append ids (List.nodup_singleton _) ?_
    simp only [List.disjoint_singleton, List.mem_map, not_exists, not_and]
    intro l present same
    exact fresh l present same
  · intro l present parent mem
    rcases List.mem_append.mp present with old | new
    · exact ordered l old parent mem
    · rw [List.mem_singleton.mp new]; exact below parent (List.mem_singleton.mp new ▸ mem)
  · intro l present
    rcases List.mem_append.mp present with old | new
    · exact covered l old
    · rw [List.mem_singleton.mp new]; exact allocated
  · intro l present id mem
    rcases List.mem_append.mp present with old | new
    · obtain ⟨p, pPresent, rest⟩ := live l old id mem
      exact ⟨p, List.mem_append_left _ pPresent, rest⟩
    · rw [List.mem_singleton.mp new] at mem ⊢
      obtain ⟨p, pPresent, rest⟩ := parents id mem
      exact ⟨p, List.mem_append_left _ pPresent, rest⟩
  · intro a aPresent b bPresent different
    rcases List.mem_append.mp aPresent with aOld | aNew <;>
      rcases List.mem_append.mp bPresent with bOld | bNew
    · exact pairs a aOld b bOld different
    · rw [List.mem_singleton.mp bNew]; exact compatible_symm (compatible a aOld)
    · rw [List.mem_singleton.mp aNew]; exact compatible b bOld
    · exact absurd ((List.mem_singleton.mp aNew).trans (List.mem_singleton.mp bNew).symm ▸ rfl) different

/-! ## Adding an allocation with its root loan -/

/-- Every loan lies in the allocation of its own root. -/
theorem covered_root {s : State} (valid : Valid s) {l : Loan} (present : l ∈ s.loans) :
    ∃ a ∈ s.allocations, a.root = l.region.root := by
  obtain ⟨a, aPresent, contains⟩ := valid.covered l present
  exact ⟨a, aPresent, contains.1⟩

/-- A new allocation and its root loan need a loan id and a root used nowhere;
the loan's storage is then apart from every other loan. A heap allocation's
release authority needs a holder that holds no authority yet. -/
theorem valid_add_root {s : State} {id count : Nat} {mode : Mode} {origin : Origin} {family : Nat}
    (valid : Valid s) (freshLoan : ∀ l ∈ s.loans, l.id ≠ id)
    (freshRoot : ∀ a ∈ s.allocations, a.root ≠ id)
    (holder : origin = .heap → ∀ t ∈ s.authorities, t.holder ≠ id) :
    Valid { s with
      loans := s.loans ++ [⟨id, ⟨id, 0, count⟩, mode, []⟩]
      allocations := s.allocations ++ [⟨id, count, origin⟩]
      authorities := if origin == .heap then s.authorities ++ [⟨id, id, family⟩] else s.authorities } := by
  have apart : ∀ l ∈ s.loans, l.region.root ≠ id := by
    intro l present same
    obtain ⟨a, aPresent, root⟩ := covered_root valid present
    exact freshRoot a aPresent (root.trans same)
  have unauthorized : ∀ t ∈ s.authorities, t.root ≠ id := by
    intro t present same
    obtain ⟨a, aPresent, root, _⟩ := valid.authoritiesHeap t present
    exact freshRoot a aPresent (root.trans same)
  obtain ⟨ids, roots, authorityRoots, ordered, covered, live, pairs, heap, holders⟩ := valid
  have extended : ∀ t ∈ s.authorities, ∃ a ∈ s.allocations ++ [⟨id, count, origin⟩],
      a.root = t.root ∧ a.origin = .heap := by
    intro t present
    obtain ⟨a, aPresent, rest⟩ := heap t present
    exact ⟨a, List.mem_append_left _ aPresent, rest⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.map_append, List.map_cons, List.map_nil]
    exact ids.append (List.nodup_singleton _) (by
      simpa [List.disjoint_singleton] using fun l present same => freshLoan l present same)
  · simp only [List.map_append, List.map_cons, List.map_nil]
    exact roots.append (List.nodup_singleton _) (by
      simpa [List.disjoint_singleton] using fun a present same => freshRoot a present same)
  · by_cases isHeap : origin = .heap
    · simp only [isHeap, beq_self_eq_true, ↓reduceIte, List.map_append, List.map_cons, List.map_nil]
      exact authorityRoots.append (List.nodup_singleton _) (by
        simpa [List.disjoint_singleton] using fun t present same => unauthorized t present same)
    · simpa [isHeap] using authorityRoots
  · intro l present parent mem
    rcases List.mem_append.mp present with old | new
    · exact ordered l old parent mem
    · simp [List.mem_singleton.mp new] at mem
  · intro l present
    rcases List.mem_append.mp present with old | new
    · obtain ⟨a, aPresent, contains⟩ := covered l old
      exact ⟨a, List.mem_append_left _ aPresent, contains⟩
    · rw [List.mem_singleton.mp new]
      exact ⟨⟨id, count, origin⟩, List.mem_append_right _ (List.mem_singleton_self _), Region.contains_refl _⟩
  · intro l present p mem
    rcases List.mem_append.mp present with old | new
    · obtain ⟨q, qPresent, rest⟩ := live l old p mem
      exact ⟨q, List.mem_append_left _ qPresent, rest⟩
    · simp [List.mem_singleton.mp new] at mem
  · have disjoint : ∀ l ∈ s.loans, Compatible ⟨id, ⟨id, 0, count⟩, mode, []⟩ l := fun l present =>
      Or.inr (Or.inr (Or.inl (Or.inl (fun same => apart l present same.symm))))
    intro a aPresent b bPresent different
    rcases List.mem_append.mp aPresent with aOld | aNew <;>
      rcases List.mem_append.mp bPresent with bOld | bNew
    · exact pairs a aOld b bOld different
    · rw [List.mem_singleton.mp bNew]; exact compatible_symm (disjoint a aOld)
    · rw [List.mem_singleton.mp aNew]; exact disjoint b bOld
    · exact absurd (by rw [List.mem_singleton.mp aNew, List.mem_singleton.mp bNew]) different
  · by_cases isHeap : origin = .heap
    · subst isHeap
      simp only [beq_self_eq_true, ↓reduceIte]
      intro t present
      rcases List.mem_append.mp present with old | new
      · exact extended t old
      · rw [List.mem_singleton.mp new]
        exact ⟨⟨id, count, .heap⟩, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl⟩
    · simpa [isHeap] using extended
  · by_cases isHeap : origin = .heap
    · simp only [isHeap, beq_self_eq_true, ↓reduceIte, List.map_append, List.map_cons, List.map_nil]
      exact holders.append (List.nodup_singleton _) (by
        simpa [List.disjoint_singleton] using fun t present same => holder isHeap t present same)
    · simpa [isHeap] using holders

/-! ## Dropping an owner whose storage nothing reaches -/

/-- Two authorities with one root are the same authority. -/
theorem authority_of_root {s : State} (valid : Valid s) {t u : ReleaseAuthority}
    (tPresent : t ∈ s.authorities) (uPresent : u ∈ s.authorities) (same : t.root = u.root) : t = u :=
  List.inj_on_of_nodup_map valid.authorityRoots tPresent uPresent same

/-- The owner `token` is dropped with its storage once no loan lies in it. -/
theorem valid_drop_owner {s : State} {token : ReleaseAuthority} (valid : Valid s)
    (held : token ∈ s.authorities) (unused : ∀ l ∈ s.loans, l.region.root ≠ token.root) :
    Valid { s with authorities := s.authorities.filter (fun a => a.holder != token.holder)
                   allocations := s.allocations.filter (fun a => a.root != token.root) } := by
  have others : ∀ t ∈ s.authorities, t.holder ≠ token.holder → t.root ≠ token.root := by
    intro t present different same
    exact different (by rw [authority_of_root valid present held same])
  obtain ⟨ids, roots, authorityRoots, ordered, covered, live, pairs, heap, holders⟩ := valid
  refine ⟨ids, roots.sublist (List.filter_sublist.map _),
    authorityRoots.sublist (List.filter_sublist.map _), ordered, ?_, live, pairs, ?_,
    holders.sublist (List.filter_sublist.map _)⟩
  · intro l present
    obtain ⟨a, aPresent, contains⟩ := covered l present
    refine ⟨a, List.mem_filter.mpr ⟨aPresent, ?_⟩, contains⟩
    simpa [Allocation.region] using fun same => unused l present (contains.1.symm.trans same)
  · intro t present
    obtain ⟨tPresent, kept⟩ := List.mem_filter.mp present
    obtain ⟨a, aPresent, root, isHeap⟩ := heap t tPresent
    refine ⟨a, List.mem_filter.mpr ⟨aPresent, ?_⟩, root, isHeap⟩
    simpa [root] using others t tPresent (by simpa using kept)

/-! ## Dropping storage nothing uses and nothing releases -/

/-- Allocations in which no loan lies and which no authority releases can be dropped. -/
theorem valid_filter_allocations {s : State} {keep : Allocation → Bool} (valid : Valid s)
    (dropped : ∀ a ∈ s.allocations, keep a = false →
      (∀ l ∈ s.loans, l.region.root ≠ a.root) ∧ a.origin ≠ .heap) :
    Valid { s with allocations := s.allocations.filter keep } := by
  obtain ⟨ids, roots, authorityRoots, ordered, covered, live, pairs, heap, holders⟩ := valid
  refine ⟨ids, roots.sublist (List.filter_sublist.map _), authorityRoots, ordered, ?_, live, pairs, ?_, holders⟩
  · intro l present
    obtain ⟨a, aPresent, contains⟩ := covered l present
    refine ⟨a, List.mem_filter.mpr ⟨aPresent, ?_⟩, contains⟩
    by_contra notKept
    exact (dropped a aPresent (by simpa using notKept)).1 l present contains.1.symm
  · intro t present
    obtain ⟨a, aPresent, root, isHeap⟩ := heap t present
    refine ⟨a, List.mem_filter.mpr ⟨aPresent, ?_⟩, root, isHeap⟩
    by_contra notKept
    exact (dropped a aPresent (by simpa using notKept)).2 isHeap

/-! ## Narrowing a loan -/

/-- A loan with no live descendant may narrow to a part of its region. -/
theorem valid_restrict {s : State} {id : Nat} {region : Region} {l : Loan} (valid : Valid s)
    (present : l ∈ s.loans) (identity : l.id = id) (inside : l.region.Contains region)
    (childless : ∀ k ∈ s.loans, id ∉ k.ancestors) :
    Valid { s with loans := s.loans.map fun loan =>
      if loan.id == id then { loan with region := region } else loan } := by
  have unique := valid.loanIds
  obtain ⟨ids, roots, authorityRoots, ordered, covered, live, pairs, heap, holders⟩ := valid
  have only : ∀ k ∈ s.loans, k.id = id → k = l := fun k kPresent same =>
    List.inj_on_of_nodup_map unique kPresent present (same.trans identity.symm)
  let narrow : Loan → Loan := fun loan => if loan.id == id then { loan with region := region } else loan
  have narrowId : ∀ k, (narrow k).id = k.id := by intro k; simp only [narrow]; split <;> rfl
  have narrowAncestors : ∀ k, (narrow k).ancestors = k.ancestors := by
    intro k; simp only [narrow]; split <;> rfl
  have narrowMode : ∀ k, (narrow k).mode = k.mode := by intro k; simp only [narrow]; split <;> rfl
  have narrowRegion : ∀ k ∈ s.loans, k.region.Contains (narrow k).region := by
    intro k kPresent; simp only [narrow]
    split
    · rename_i same
      rw [only k kPresent (by simpa using same)]; exact inside
    · exact Region.contains_refl _
  have mapIds : (s.loans.map narrow).map LoanOf.id = s.loans.map LoanOf.id := by
    simp [List.map_map, Function.comp_def, narrowId]
  refine ⟨mapIds ▸ ids, roots, authorityRoots, ?_, ?_, ?_, ?_, heap, holders⟩
  · intro k kPresent parent mem
    obtain ⟨k', k'Present, rfl⟩ := List.mem_map.mp kPresent
    rw [narrowId]; rw [narrowAncestors] at mem
    exact ordered k' k'Present parent mem
  · intro k kPresent
    obtain ⟨k', k'Present, rfl⟩ := List.mem_map.mp kPresent
    obtain ⟨a, aPresent, contains⟩ := covered k' k'Present
    exact ⟨a, aPresent, Region.contains_trans contains (narrowRegion k' k'Present)⟩
  · intro k kPresent p mem
    obtain ⟨k', k'Present, rfl⟩ := List.mem_map.mp kPresent
    rw [narrowAncestors] at mem
    obtain ⟨q, qPresent, qId, contains, mode⟩ := live k' k'Present p mem
    have qOther : q.id ≠ id := fun same => childless k' k'Present (by rw [← same, qId]; exact mem)
    have qSame : narrow q = q := by
      simp only [narrow]; split
      · rename_i same; exact absurd (by simpa using same) qOther
      · rfl
    refine ⟨q, List.mem_map.mpr ⟨q, qPresent, qSame⟩, qId,
      Region.contains_trans contains (narrowRegion k' k'Present), ?_⟩
    rw [narrowMode]; exact mode
  · intro a aPresent b bPresent different
    obtain ⟨a', a'Present, rfl⟩ := List.mem_map.mp aPresent
    obtain ⟨b', b'Present, rfl⟩ := List.mem_map.mp bPresent
    rw [narrowId, narrowId] at different
    rcases pairs a' a'Present b' b'Present different with h | h | h | h
    · exact Or.inl (by rw [narrowId, narrowAncestors]; exact h)
    · exact Or.inr (Or.inl (by rw [narrowId, narrowAncestors]; exact h))
    · exact Or.inr (Or.inr (Or.inl (Region.disjoint_subregions h
        (narrowRegion a' a'Present) (narrowRegion b' b'Present))))
    · exact Or.inr (Or.inr (Or.inr (by rw [narrowMode, narrowMode]; exact h)))

/-! ## Renaming an authority's holder -/

/-- A release authority may pass to a holder that holds none. -/
theorem valid_rename_holder {s : State} {old fresh : Nat} (valid : Valid s)
    (free : ∀ t ∈ s.authorities, t.holder ≠ fresh) :
    Valid { s with authorities := s.authorities.map fun t =>
      if t.holder == old then t.move fresh else t } := by
  obtain ⟨ids, roots, authorityRoots, ordered, covered, live, pairs, heap, holders⟩ := valid
  let rename : ReleaseAuthority → ReleaseAuthority := fun t => if t.holder == old then t.move fresh else t
  have renameRoot : ∀ t, (rename t).root = t.root := by
    intro t; simp only [rename]; split <;> rfl
  have renameHolder : ∀ t, (rename t).holder = if t.holder = old then fresh else t.holder := by
    intro t; by_cases h : t.holder = old <;> simp [rename, h, ReleaseAuthority.move]
  refine ⟨ids, roots, ?_, ordered, covered, live, pairs, ?_, ?_⟩
  · show ((s.authorities.map rename).map ReleaseAuthority.root).Nodup
    have rootsMapped : (s.authorities.map rename).map ReleaseAuthority.root =
        s.authorities.map ReleaseAuthority.root := by
      simp only [List.map_map]; congr 1; funext t; exact renameRoot t
    rw [rootsMapped]; exact authorityRoots
  · intro t present
    obtain ⟨t', t'Present, rfl⟩ := List.mem_map.mp present
    obtain ⟨a, aPresent, root, isHeap⟩ := heap t' t'Present
    exact ⟨a, aPresent, root.trans (renameRoot t').symm, isHeap⟩
  · have mapped : (s.authorities.map rename).map ReleaseAuthority.holder =
        (s.authorities.map ReleaseAuthority.holder).map (fun h => if h = old then fresh else h) := by
      simp only [List.map_map]
      congr 1; funext t
      exact renameHolder t
    rw [mapped]
    refine holders.map_on ?_
    intro x xIn y yIn same
    obtain ⟨tx, txIn, rfl⟩ := List.mem_map.mp xIn
    obtain ⟨ty, tyIn, rfl⟩ := List.mem_map.mp yIn
    by_cases hx : tx.holder = old <;> by_cases hy : ty.holder = old <;> simp only [hx, hy, ↓reduceIte] at same
    · rw [hx, hy]
    · exact absurd same.symm (free ty tyIn)
    · exact absurd same (free tx txIn)
    · exact same

/-! ## What a step's own checks establish -/

theorem findLoan_some {s : State} {id : Nat} {l : Loan} (h : findLoan s id = some l) :
    l ∈ s.loans ∧ l.id = id := by
  unfold findLoan at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem findAuthority_some {s : State} {holder : Nat} {token : ReleaseAuthority}
    (h : findAuthority s holder = some token) : token ∈ s.authorities ∧ token.holder = holder :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem fresh_loans {s : State} {id : Nat} (h : fresh s id = true) : ∀ l ∈ s.loans, l.id ≠ id := by
  unfold fresh at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at h
  exact h.1

theorem holderFree_true {s : State} {holder : Nat} (h : holderFree s holder = true) :
    ∀ t ∈ s.authorities, t.holder ≠ holder := by
  unfold holderFree at h
  simpa [List.any_eq_false] using h

theorem rootFree_true {loans : List Loan} {root : Nat} (h : rootFree loans root = true) :
    ∀ l ∈ loans, l.region.root ≠ root := by
  unfold rootFree at h
  simpa [List.any_eq_false] using h

theorem tokenRoot_of_find {s : State} {holder : Nat} {token : ReleaseAuthority}
    (h : findAuthority s holder = some token) : tokenRoot s holder = some token.root := by
  simp [tokenRoot, h]

/-- A step that drops the root `root` from the allocations and passed its local
check leaves no loan in it. -/
theorem unused_of_keptOrUnused {after : State} {root : Nat}
    (gone : ∀ a ∈ after.allocations, a.root ≠ root) (h : keptOrUnused after root = true) :
    ∀ l ∈ after.loans, l.region.root ≠ root := by
  unfold keptOrUnused at h
  rcases Bool.or_eq_true_iff.mp h with kept | unused
  · obtain ⟨a, present, same⟩ := List.any_eq_true.mp kept
    exact absurd (by simpa using same) (gone a present)
  · exact rootFree_true unused

/-! ## Each action -/

theorem root_preserves_valid {s after : State} {id count : Nat} {mode : Mode} {origin : Origin}
    {family : Nat} (valid : Valid s) (step : transition s (.root id count mode origin family) = some after)
    (checked : localCheck s (.root id count mode origin family) after = true) : Valid after := by
  obtain ⟨_, first, rest⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  have c := require_some first
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at c
  refine valid_add_root valid (fresh_loans c.1.2) c.2 ?_
  intro isHeap
  simp only [localCheck, isHeap, bne_self_eq_false, Bool.false_or] at checked
  exact holderFree_true checked

theorem borrow_preserves_valid {s after : State} {id parent : Nat} {region : Region} {mode : Mode}
    (valid : Valid s) (step : transition s (.borrow id parent region mode) = some after) :
    Valid after := by
  obtain ⟨p, found, rest⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨_, checks, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, accessed, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  obtain ⟨pPresent, pId⟩ := findLoan_some found
  have c := require_some checks
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at c
  obtain ⟨⟨isFresh, parentBelow⟩, ancestorsBelow⟩ := c
  obtain ⟨l, lPresent, lId, lContains, lMode, lOthers⟩ := require_access accessed
  have lp : l = p := List.inj_on_of_nodup_map valid.loanIds lPresent pPresent (lId.trans pId.symm)
  subst lp
  -- the new loan's mode is allowed by its parent, hence by every ancestor
  have allowed : l.mode = .shared → mode = .shared := by
    intro shared
    cases mode with
    | shared => rfl
    | exclusive => exact absurd (lMode (by decide)) (by rw [shared]; decide)
  apply valid_add_loan valid (fresh_loans isFresh)
  · intro q mem
    rcases List.mem_cons.mp mem with rfl | old
    · exact parentBelow
    · exact ancestorsBelow q old
  · obtain ⟨a, aPresent, contains⟩ := valid.covered l lPresent
    exact ⟨a, aPresent, Region.contains_trans contains lContains⟩
  · intro q mem
    rcases List.mem_cons.mp mem with rfl | old
    · exact ⟨l, lPresent, lId, lContains, allowed⟩
    · obtain ⟨k, kPresent, kId, kContains, kMode⟩ := valid.ancestorsLive l lPresent q old
      exact ⟨k, kPresent, kId, Region.contains_trans kContains lContains,
        fun shared => allowed (kMode shared)⟩
  · intro k kPresent
    by_cases isParent : k.id = parent
    · exact Or.inr (Or.inl (List.mem_cons.mpr (Or.inl isParent)))
    · by_cases apart : region.Disjoint k.region
      · exact Or.inr (Or.inr (Or.inl apart))
      · rcases lOthers k kPresent isParent apart with ancestor | ⟨reading, shared⟩
        · exact Or.inr (Or.inl (List.mem_cons.mpr (Or.inr ancestor)))
        · refine Or.inr (Or.inr (Or.inr ⟨?_, shared⟩))
          cases mode with
          | shared => rfl
          | exclusive => simp at reading

theorem endLoan_preserves_valid {s after : State} {id : Nat} (valid : Valid s)
    (step : transition s (.endLoan id) = some after)
    (checked : localCheck s (.endLoan id) after = true) : Valid after := by
  obtain ⟨_, first, rest⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨l, _, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  have c := require_some first
  simp only [Bool.and_eq_true, mayEndB_iff] at c
  have erased : Valid (eraseLoan s id) := valid_erase valid c.2.2
  refine valid_filter_allocations erased ?_
  intro a aPresent dropped
  simp only [Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at dropped
  obtain ⟨⟨rootIsL, rootIsId⟩, notHeap⟩ := dropped
  refine ⟨?_, notHeap⟩
  -- the root `id` is no longer allocated, so the local check leaves no loan in it
  have gone : ∀ b ∈ (eraseLoan s id).allocations.filter
      (fun a => !(a.root == l.region.root && id == a.root && a.origin != .heap)), b.root ≠ id := by
    intro b bPresent same
    obtain ⟨bOld, kept⟩ := List.mem_filter.mp bPresent
    have ba : b = a := List.inj_on_of_nodup_map valid.allocationRoots bOld aPresent (same.trans rootIsId)
    rw [ba] at kept
    have dropping : (a.root == l.region.root && id == a.root && a.origin != .heap) = true := by
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
      exact ⟨⟨rootIsL, rootIsId⟩, notHeap⟩
    rw [dropping] at kept
    exact absurd kept (by decide)
  have unused := unused_of_keptOrUnused gone checked
  rw [← rootIsId]
  exact unused

theorem move_preserves_valid {s after : State} {old freshId : Nat} (valid : Valid s)
    (step : transition s (.move old freshId) = some after)
    (checked : localCheck s (.move old freshId) after = true) : Valid after := by
  obtain ⟨l, found, rest⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨_, first, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, second, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  obtain ⟨lPresent, lId⟩ := findLoan_some found
  have c := require_some first
  simp only [Bool.and_eq_true, mayEndB_iff] at c
  obtain ⟨⟨_, isFresh⟩, mayEnd⟩ := c
  have below := require_some second
  simp only [List.all_eq_true, decide_eq_true_eq] at below
  have erased : Valid (eraseLoan s old) := valid_erase valid mayEnd.2
  have added := valid_add_loan (n := { l with id := freshId }) erased
    (fun k kPresent => fresh_loans isFresh k (mem_endLoan.mp kPresent).1) below
    (valid.covered l lPresent)
    (by
      intro p mem
      obtain ⟨q, qPresent, qId, rest⟩ := valid.ancestorsLive l lPresent p mem
      have qOld : q.id ≠ old := by
        rw [qId, ← lId]; exact Nat.ne_of_lt (valid.ordered l lPresent p mem)
      exact ⟨q, mem_endLoan.mpr ⟨qPresent, qOld⟩, qId, rest⟩)
    (by
      intro k kPresent
      obtain ⟨kOld, kOther⟩ := mem_endLoan.mp kPresent
      rcases valid.compatible l lPresent k kOld (by rw [lId]; exact fun h => kOther h.symm) with
        h | h | h | h
      · exact absurd (lId ▸ h) (mayEnd.2 k kOld)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h)))
  exact valid_rename_holder added (holderFree_true checked)

theorem restrict_preserves_valid {s after : State} {id : Nat} {region : Region} (valid : Valid s)
    (step : transition s (.restrict id region) = some after) : Valid after := by
  obtain ⟨l, found, rest⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨_, first, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  obtain ⟨lPresent, lId⟩ := findLoan_some found
  have c := require_some first
  simp only [Bool.and_eq_true, mayEndB_iff] at c
  exact valid_restrict valid lPresent lId ((containsB_iff _ _).mp c.1.2) c.2.2

/-- Giving up an owner: its own loan ends, then its authority and storage go,
once its local check showed no other loan in that storage. -/
theorem valid_give_up {s : State} {holder : Nat} {token : ReleaseAuthority} (valid : Valid s)
    (found : s.authorities.find? (fun a => a.holder == holder) = some token)
    (childless : ∀ l ∈ s.loans, holder ∉ l.ancestors)
    (unused : ∀ l ∈ endLoan s.loans holder, l.region.root ≠ token.root) :
    Valid { s with loans := endLoan s.loans holder
                   authorities := s.authorities.filter fun a => a.holder != holder
                   allocations := s.allocations.filter fun a => a.root != token.root } := by
  obtain ⟨held, holderEq⟩ := findAuthority_some found
  subst holderEq
  exact valid_drop_owner (valid_erase valid childless) held unused

/-- The local check of an owner given up: no loan left in its storage. -/
theorem given_up_unused {s : State} {token : ReleaseAuthority} {a : Action} {after : State}
    (shape : localCheck s a after = keptOrUnused after token.root)
    (gone : after.allocations = s.allocations.filter fun a => a.root != token.root)
    (checked : localCheck s a after = true) : ∀ l ∈ after.loans, l.region.root ≠ token.root := by
  refine unused_of_keptOrUnused ?_ (shape ▸ checked)
  intro b bPresent
  rw [gone] at bPresent
  simpa using (List.mem_filter.mp bPresent).2

theorem give_preserves_valid {s after : State} {holder family : Nat} (valid : Valid s)
    (step : transition s (.give holder family) = some after)
    (checked : localCheck s (.give holder family) after = true) : Valid after := by
  obtain ⟨token, found, rest⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, may, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  have unused := given_up_unused (by simp [localCheck, tokenRoot_of_find found]) rfl checked
  refine (valid_congr ?_ ?_ ?_).mp
    (valid_give_up valid found (require_mayEnd may).2 unused) <;> rfl

theorem handoff_preserves_valid {s after : State} {holder family : Nat} (valid : Valid s)
    (step : transition s (.handoff holder family) = some after)
    (checked : localCheck s (.handoff holder family) after = true) : Valid after := by
  obtain ⟨token, found, rest⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, may, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  have unused := given_up_unused (by simp [localCheck, tokenRoot_of_find found]) rfl checked
  refine (valid_congr ?_ ?_ ?_).mp
    (valid_give_up valid found (require_mayEnd may).2 unused) <;> rfl

theorem recordGive_preserves_valid {s after : State} {key holder family : Nat} (valid : Valid s)
    (step : transition s (.recordGive key holder family) = some after)
    (checked : localCheck s (.recordGive key holder family) after = true) : Valid after := by
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨token, found, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, may, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  have unused := given_up_unused (by simp [localCheck, tokenRoot_of_find found]) rfl checked
  refine (valid_congr ?_ ?_ ?_).mp
    (valid_give_up valid found (require_mayEnd may).2 unused) <;> rfl

theorem replace_preserves_valid {s after : State} {view holder family : Nat} (valid : Valid s)
    (step : transition s (.replace view holder family) = some after)
    (checked : localCheck s (.replace view holder family) after = true) : Valid after := by
  obtain ⟨token, found, rest⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, may, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  have unused := given_up_unused (by simp [localCheck, tokenRoot_of_find found]) rfl checked
  refine (valid_congr ?_ ?_ ?_).mp
    (valid_give_up valid found (require_mayEnd may).2 unused) <;> rfl

theorem release_preserves_valid {s after : State} {holder family : Nat} (valid : Valid s)
    (step : transition s (.release holder family) = some after) : Valid after := by
  obtain ⟨token, found, rest⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨_, may, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  obtain ⟨held, holderEq⟩ := findAuthority_some found
  have dropped := valid_drop_owner valid held (require_mayRelease may).2.2
  subst holderEq
  refine (valid_congr ?_ ?_ ?_).mp dropped <;> rfl

theorem nullOwner_preserves_valid {s after : State} {holder family : Nat} (valid : Valid s)
    (step : transition s (.nullOwner holder family) = some after) : Valid after := by
  obtain ⟨token, found, rest⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨_, may, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  obtain ⟨held, holderEq⟩ := findAuthority_some found
  have dropped := valid_drop_owner valid held (require_mayRelease may).2.2
  subst holderEq
  refine (valid_congr ?_ ?_ ?_).mp dropped <;> rfl

theorem vacate_preserves_valid {s after : State} {view family : Nat} (valid : Valid s)
    (step : transition s (.vacate view family) = some after) : Valid after := by
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  refine (valid_congr ?_ ?_ ?_).mp valid <;> rfl

theorem restore_preserves_valid {s after : State} {view : Nat} (valid : Valid s)
    (step : transition s (.restore view) = some after) : Valid after := by
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  refine (valid_congr ?_ ?_ ?_).mp valid <;> rfl

/-! ## Every step -/

/-- A step whose local check passes keeps the invariant. -/
theorem transition_preserves_valid {s after : State} {a : Action} (valid : Valid s)
    (step : transition s a = some after) (checked : localCheck s a after = true) : Valid after := by
  cases a <;> first
    | exact root_preserves_valid valid step checked
    | exact borrow_preserves_valid valid step
    | exact endLoan_preserves_valid valid step checked
    | exact move_preserves_valid valid step checked
    | exact restrict_preserves_valid valid step
    | exact release_preserves_valid valid step
    | exact give_preserves_valid valid step checked
    | exact handoff_preserves_valid valid step checked
    | exact recordGive_preserves_valid valid step checked
    | exact replace_preserves_valid valid step checked
    | exact vacate_preserves_valid valid step
    | exact restore_preserves_valid valid step
    | exact nullOwner_preserves_valid valid step
    | exact metadata_preserves_valid rfl step valid

/-! ## The local check holds in every valid result -/

/-- In a valid state every loan lies in an allocation of its root, so a root is
still allocated or no loan is left in it. -/
theorem keptOrUnused_of_valid {after : State} (valid : Valid after) (root : Nat) :
    keptOrUnused after root = true := by
  unfold keptOrUnused rootFree
  by_cases kept : after.allocations.any (fun a => a.root == root) = true
  · simp [kept]
  · rw [Bool.eq_false_iff.mpr kept, Bool.false_or]
    simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
    intro l present same
    obtain ⟨a, aPresent, root'⟩ := covered_root valid present
    exact kept (List.any_eq_true.mpr ⟨a, aPresent, by simpa using root'.trans same⟩)

theorem root_check_of_valid {s after : State} {id count : Nat} {mode : Mode} {origin : Origin}
    {family : Nat} (step : transition s (.root id count mode origin family) = some after)
    (validAfter : Valid after) : localCheck s (.root id count mode origin family) after = true := by
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  simp only [localCheck]
  by_cases isHeap : origin = .heap
  · subst isHeap
    have holders := validAfter.holders
    simp only [beq_self_eq_true, ↓reduceIte, List.map_append, List.map_cons, List.map_nil] at holders
    simp only [bne_self_eq_false, Bool.false_or, holderFree, Bool.not_eq_true', List.any_eq_false,
      beq_iff_eq]
    intro t present same
    exact (List.nodup_append.mp holders).2.2 _ (List.mem_map.mpr ⟨t, present, rfl⟩) _
      (List.mem_singleton_self _) same
  · simp [isHeap]

theorem move_check_of_valid {s after : State} {old freshId : Nat}
    (step : transition s (.move old freshId) = some after) (validAfter : Valid after) :
    localCheck s (.move old freshId) after = true := by
  obtain ⟨l, found, rest⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨_, first, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, holding, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  obtain ⟨lPresent, lId⟩ := findLoan_some found
  have c := require_some first
  simp only [Bool.and_eq_true, mayEndB_iff] at c
  have distinct : freshId ≠ old := fun same => fresh_loans c.1.2 l lPresent (lId.trans same.symm)
  obtain ⟨token, tokenPresent, tokenHolder⟩ := List.any_eq_true.mp (require_some holding)
  simp only [beq_iff_eq] at tokenHolder
  have holders := validAfter.holders
  simp only [List.map_map] at holders
  simp only [localCheck, holderFree, Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
  intro t present same
  have equal := List.inj_on_of_nodup_map holders present tokenPresent (by
    simp [same, tokenHolder, distinct, ReleaseAuthority.move])
  exact distinct (same.symm.trans (equal ▸ tokenHolder))

/-- The local check of a step holds exactly when the invariant still holds. -/
theorem localCheck_of_valid {s after : State} {a : Action} (step : transition s a = some after)
    (validAfter : Valid after) : localCheck s a after = true := by
  cases a <;> first
    | exact root_check_of_valid step validAfter
    | exact move_check_of_valid step validAfter
    | exact keptOrUnused_of_valid validAfter _
    | (simp only [localCheck]; split <;> simp [keptOrUnused_of_valid validAfter])
    | rfl

theorem localCheck_iff_valid {s after : State} {a : Action} (valid : Valid s)
    (step : transition s a = some after) : localCheck s a after = true ↔ Valid after :=
  ⟨transition_preserves_valid valid step, localCheck_of_valid step⟩

/-- From a valid state, the local check decides exactly what the check of the
whole invariant decides: replacing one by the other changes no step's outcome. -/
theorem localCheck_eq_validB {s after : State} {a : Action} (valid : Valid s)
    (step : transition s a = some after) : localCheck s a after = validB after := by
  rw [Bool.eq_iff_iff, localCheck_iff_valid valid step, validB_iff]

/-! ## Steps -/

/-- A step keeps the invariant: the transition followed by its local check. -/
theorem apply_preserves_valid {s after : State} {a : Action}
    (h : apply s a = some after) (valid : Valid s) : Valid after :=
  transition_preserves_valid valid (apply_transition h) (apply_localCheck h)

/-- From a valid state, a step decides exactly what the transition followed by a
check of the whole invariant decides. -/
theorem apply_eq_globally_checked {s : State} (valid : Valid s) (a : Action) :
    apply s a = (transition s a).bind fun after =>
      (require (validB after)).bind fun _ => some after := by
  unfold apply
  cases step : transition s a with
  | none => rfl
  | some after => simp only [Option.bind_some, localCheck_eq_validB valid step]

end Mettapedia.Ownership
