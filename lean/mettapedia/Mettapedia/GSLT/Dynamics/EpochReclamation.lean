import Mettapedia.GSLT.Dynamics.StoreReachability

/-!
# Epoch reclamation of decoded copies

A store keeps durable terms and collects them by reachability.  Reading a
term hands out a *decoded copy*: a pointer graph in a dynamic heap, cheaper
to read than the store's records and shared by every later reader.  A holder
may keep a decoded copy after the term it copies is collected, so copies
cannot be freed together with their terms.  This module proves the protocol
that frees them anyway, without stopping or tracing other holders.

Cells live in the **static** region (never collected), in an **epoch** of the
dynamic heap, or in an **owner**'s own collected storage.  Each owner records
the set of epochs whose cells it may point into.  The protocol keeps four
disciplines:

* static cells point only to static cells (`staticClosed`): storing into
  static storage copies dynamic children instead of sharing them;
* an epoch's cells point only into the same epoch or into static storage
  (`epochClosed`), and the cache slots point only into the current epoch
  (`slotsCurrent`): closing an epoch clears every slot, so later copies are
  decoded afresh;
* an owner's roots and its own cells point only into epochs of its set
  (`ownerRoots`, `ownedBounded`).

Results:

* **Safety** (`freeable_unreachable`): an epoch that is not current and that
  no live owner holds contains no reachable cell.
* **Invisibility** (`free_reach_iff`): removing such an epoch changes no
  reachability, so no observation that factors through the reachable part.
* **Retention** (`reachable_epoch_held`): a reachable cell of an epoch lies
  in the current epoch or in an epoch some live owner holds, so the memory
  retained is the current epoch's plus the held ones'.
* **Preservation**: decoding, reading, building static or owned storage,
  closing an epoch, widening an owner's set (a holder that ends hands its set
  to the one below; a cursor that stops running lends its set to its host,
  whose goals share its copies; a host hands values to a cursor), an owner's
  collection (which may shrink its set to what it still points into: a host
  that returns its storage to a mark returns to its set at that mark), an
  owner's exit and freeing an epoch all keep the disciplines.
* **Necessity** (`shared_copy_resurrects`): a static root that shares a
  decoded copy keeps an epoch that no owner holds reachable.

The concrete collector (CeTTa's decoded-copy epochs) realizes each operation:
an owner's set is a word with one bit per unfreed epoch.  Agreement between
its C visitors and these operations is checked by poisoned reclamation and
growth tests, not by this model.
-/

namespace Mettapedia.GSLT.Dynamics.EpochReclamation

open Mettapedia.GSLT.Dynamics.StoreReachability

/-- Where a cell lives. -/
inductive Region (Owner : Type) where
  | static : Region Owner
  | epoch : ℕ → Region Owner
  | owned : Owner → Region Owner

variable {Cell Owner : Type}

/-- A heap with its reclamation state: the current epoch and, for each owner,
the epochs whose cells it may point into. -/
structure Heap (Cell Owner : Type) where
  region : Cell → Region Owner
  pointsTo : Cell → Cell → Prop
  staticRoot : Cell → Prop
  slot : Cell → Prop
  ownerRoot : Owner → Cell → Prop
  live : Owner → Prop
  current : ℕ
  holds : Owner → ℕ → Prop

namespace Heap

/-- The store whose reachability decides liveness: static roots, cache slots
and live owners' roots. -/
def store (H : Heap Cell Owner) : Store Cell where
  pointsTo := H.pointsTo
  root c := H.staticRoot c ∨ H.slot c ∨ ∃ o, H.live o ∧ H.ownerRoot o c

/-- A cell an owner may point to: static, its own, or in an epoch it holds. -/
def OwnerTarget (H : Heap Cell Owner) (o : Owner) (c : Cell) : Prop :=
  H.region c = .static ∨ H.region c = .owned o ∨
    ∃ e, H.region c = .epoch e ∧ H.holds o e

/-- The protocol's disciplines. -/
structure WellFormed (H : Heap Cell Owner) : Prop where
  staticClosed : ∀ {c d}, H.pointsTo c d → H.region c = .static → H.region d = .static
  epochClosed : ∀ {c d e}, H.pointsTo c d → H.region c = .epoch e →
    H.region d = .epoch e ∨ H.region d = .static
  staticRoots : ∀ {c}, H.staticRoot c → H.region c = .static
  slotsCurrent : ∀ {c}, H.slot c → H.region c = .epoch H.current
  ownerRoots : ∀ {o c}, H.live o → H.ownerRoot o c → H.OwnerTarget o c
  ownedBounded : ∀ {o c d}, H.pointsTo c d → H.region c = .owned o → H.OwnerTarget o d

/-- An epoch that may be freed: not current, and held by no live owner. -/
def Freeable (H : Heap Cell Owner) (e : ℕ) : Prop :=
  e ≠ H.current ∧ ∀ o, H.live o → ¬ H.holds o e

/-- What a reachable cell can be. -/
def Good (H : Heap Cell Owner) (c : Cell) : Prop :=
  H.region c = .static ∨ H.region c = .epoch H.current ∨
    ∃ o, H.live o ∧ H.OwnerTarget o c

theorem reach_good {H : Heap Cell Owner} (hw : H.WellFormed) {c : Cell}
    (h : Reach H.store c) : H.Good c := by
  induction h with
  | root hr =>
    rcases hr with hs | hs | ⟨o, hl, ho⟩
    · exact Or.inl (hw.staticRoots hs)
    · exact Or.inr (Or.inl (hw.slotsCurrent hs))
    · exact Or.inr (Or.inr ⟨o, hl, hw.ownerRoots hl ho⟩)
  | @step a b _ hab ih =>
    rcases ih with hs | he | ⟨o, hl, hs | ho | ⟨e, he, hheld⟩⟩
    · exact Or.inl (hw.staticClosed hab hs)
    · rcases hw.epochClosed hab he with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inl h'
    · exact Or.inl (hw.staticClosed hab hs)
    · exact Or.inr (Or.inr ⟨o, hl, hw.ownedBounded hab ho⟩)
    · rcases hw.epochClosed hab he with h' | h'
      · exact Or.inr (Or.inr ⟨o, hl, Or.inr (Or.inr ⟨e, h', hheld⟩)⟩)
      · exact Or.inl h'

/-- **Safety**: a freeable epoch holds no reachable cell. -/
theorem freeable_unreachable {H : Heap Cell Owner} (hw : H.WellFormed) {e : ℕ}
    (hf : H.Freeable e) {c : Cell} (h : Reach H.store c) : H.region c ≠ .epoch e := by
  intro hc
  rcases reach_good hw h with hs | hcur | ⟨o, hl, hs | ho | ⟨e', he', hheld⟩⟩
  · rw [hc] at hs; cases hs
  · rw [hc] at hcur
    cases hcur
    exact hf.1 rfl
  · rw [hc] at hs; cases hs
  · rw [hc] at ho; cases ho
  · rw [hc] at he'
    cases he'
    exact hf.2 o hl hheld

/-- **Retention**: a reachable cell of an epoch lies in the current epoch or
in one a live owner holds. -/
theorem reachable_epoch_held {H : Heap Cell Owner} (hw : H.WellFormed) {c : Cell} {e : ℕ}
    (h : Reach H.store c) (hc : H.region c = .epoch e) :
    e = H.current ∨ ∃ o, H.live o ∧ H.holds o e := by
  by_cases hcur : e = H.current
  · exact Or.inl hcur
  · by_cases hheld : ∃ o, H.live o ∧ H.holds o e
    · exact Or.inr hheld
    · exact absurd hc (freeable_unreachable hw
        ⟨hcur, fun o hl ho => hheld ⟨o, hl, ho⟩⟩ h)

/-- Removing epoch `e`: its cells lose every edge and every root. -/
def free (H : Heap Cell Owner) (e : ℕ) : Heap Cell Owner where
  region := H.region
  pointsTo c d := H.pointsTo c d ∧ H.region c ≠ .epoch e ∧ H.region d ≠ .epoch e
  staticRoot c := H.staticRoot c ∧ H.region c ≠ .epoch e
  slot c := H.slot c ∧ H.region c ≠ .epoch e
  ownerRoot o c := H.ownerRoot o c ∧ H.region c ≠ .epoch e
  live := H.live
  current := H.current
  holds := H.holds

theorem reach_free_mono {H : Heap Cell Owner} {e : ℕ} {c : Cell}
    (h : Reach (H.free e).store c) : Reach H.store c := by
  induction h with
  | root hr =>
    rcases hr with ⟨hs, _⟩ | ⟨hs, _⟩ | ⟨o, hl, ho, _⟩
    · exact Reach.root (Or.inl hs)
    · exact Reach.root (Or.inr (Or.inl hs))
    · exact Reach.root (Or.inr (Or.inr ⟨o, hl, ho⟩))
  | step _ hab ih => exact Reach.step ih hab.1

/-- **Invisibility**: freeing a freeable epoch changes no reachability. -/
theorem free_reach_iff {H : Heap Cell Owner} (hw : H.WellFormed) {e : ℕ}
    (hf : H.Freeable e) (c : Cell) : Reach (H.free e).store c ↔ Reach H.store c := by
  refine ⟨reach_free_mono, fun h => ?_⟩
  induction h with
  | root hr =>
    have hne := freeable_unreachable hw hf (Reach.root hr)
    rcases hr with hs | hs | ⟨o, hl, ho⟩
    · exact Reach.root (Or.inl ⟨hs, hne⟩)
    · exact Reach.root (Or.inr (Or.inl ⟨hs, hne⟩))
    · exact Reach.root (Or.inr (Or.inr ⟨o, hl, ho, hne⟩))
  | @step a b ha hab ih =>
    exact Reach.step ih ⟨hab, freeable_unreachable hw hf ha,
      freeable_unreachable hw hf (Reach.step ha hab)⟩

/-- Freeing keeps the disciplines. -/
theorem free_wellFormed {H : Heap Cell Owner} (hw : H.WellFormed) (e : ℕ) :
    (H.free e).WellFormed where
  staticClosed h hs := hw.staticClosed h.1 hs
  epochClosed h he := hw.epochClosed h.1 he
  staticRoots h := hw.staticRoots h.1
  slotsCurrent h := hw.slotsCurrent h.1
  ownerRoots hl h := hw.ownerRoots hl h.1
  ownedBounded h ho := hw.ownedBounded h.1 ho

/-! ## The operations keep the disciplines -/

/-- Closing the current epoch: the epoch `next` becomes current, and every
cache slot is cleared.  The numbers are names; the implementation skips one
an unfreed epoch still uses. -/
def close (H : Heap Cell Owner) (next : ℕ) : Heap Cell Owner :=
  { H with current := next, slot := fun _ => False }

theorem close_wellFormed {H : Heap Cell Owner} (hw : H.WellFormed) (next : ℕ) :
    (H.close next).WellFormed where
  staticClosed := hw.staticClosed
  epochClosed := hw.epochClosed
  staticRoots := hw.staticRoots
  slotsCurrent h := h.elim
  ownerRoots := hw.ownerRoots
  ownedBounded := hw.ownedBounded

/-- Widening owners' sets: a holder that ends hands its set to the holder
below it, a cursor that stops running lends its set to its host, and a host
hands a cursor values that share its copies. -/
def widen (H : Heap Cell Owner) (more : Owner → ℕ → Prop) : Heap Cell Owner :=
  { H with holds := fun o e => H.holds o e ∨ more o e }

theorem widen_wellFormed {H : Heap Cell Owner} (hw : H.WellFormed)
    (more : Owner → ℕ → Prop) : (H.widen more).WellFormed := by
  have target : ∀ {o c}, H.OwnerTarget o c → (H.widen more).OwnerTarget o c :=
    fun {o c} ht => by
      rcases ht with hs | ho | ⟨e, he, hheld⟩
      · exact Or.inl hs
      · exact Or.inr (Or.inl ho)
      · exact Or.inr (Or.inr ⟨e, he, Or.inl hheld⟩)
  exact
    { staticClosed := hw.staticClosed
      epochClosed := hw.epochClosed
      staticRoots := hw.staticRoots
      slotsCurrent := hw.slotsCurrent
      ownerRoots := fun hl h => target (hw.ownerRoots hl h)
      ownedBounded := fun h ho => target (hw.ownedBounded h ho) }

/-- An owner's collection, stated as its contract: storage that is not the
owner's keeps its region, edges and roots; other owners keep their sets; and
every root and edge of the owner then targets static storage, the owner's own
storage, or an epoch of the owner's new set.  The new set may be smaller: a
collection that copies an epoch's cells into the owner's storage drops it,
and a host that returns its storage to a mark, releasing what it made after
it, returns to the set it had there: what its goals read and what cursors
lent it with them. -/
structure Collected (H H' : Heap Cell Owner) (o : Owner) : Prop where
  current : H'.current = H.current
  holdsOther : ∀ {o'}, o' ≠ o → H'.holds o' = H.holds o'
  live : ∀ {o'}, H'.live o' ↔ H.live o'
  region : ∀ {c}, H.region c ≠ .owned o → H'.region c = H.region c
  regionNew : ∀ {c}, H'.region c ≠ H.region c → H'.region c = .owned o
  edges : ∀ {c d}, H.region c ≠ .owned o → (H'.pointsTo c d ↔ H.pointsTo c d)
  staticRoot : ∀ {c}, H'.staticRoot c ↔ H.staticRoot c
  slot : ∀ {c}, H'.slot c ↔ H.slot c
  otherRoots : ∀ {o' c}, o' ≠ o → (H'.ownerRoot o' c ↔ H.ownerRoot o' c)
  ownRoots : ∀ {c}, H'.ownerRoot o c → H'.OwnerTarget o c
  ownEdges : ∀ {c d}, H'.pointsTo c d → H'.region c = .owned o → H'.OwnerTarget o d

/-- A cell outside the collecting owner's storage after the collection was
outside it before. -/
theorem Collected.not_owned {H H' : Heap Cell Owner} {o : Owner} (hc : Collected H H' o)
    {c : Cell} (h : H'.region c ≠ .owned o) : H.region c ≠ .owned o := fun hco =>
  h (hc.regionNew (fun heq => h (heq.trans hco)))

/-- Another owner's targets keep their meaning across a collection. -/
theorem Collected.transfer {H H' : Heap Cell Owner} {o o' : Owner} {d : Cell}
    (hc : Collected H H' o) (ho : o' ≠ o) (ht : H.OwnerTarget o' d) : H'.OwnerTarget o' d := by
  rcases ht with hs | hd | ⟨e, he, hheld⟩
  · have hnd : H.region d ≠ .owned o := by rw [hs]; exact fun h' => by cases h'
    exact Or.inl (by rw [hc.region hnd, hs])
  · have hnd : H.region d ≠ .owned o := by
      rw [hd]; exact fun h' => by cases h'; exact ho rfl
    exact Or.inr (Or.inl (by rw [hc.region hnd, hd]))
  · have hnd : H.region d ≠ .owned o := by rw [he]; exact fun h' => by cases h'
    exact Or.inr (Or.inr ⟨e, by rw [hc.region hnd, he], by rw [hc.holdsOther ho]; exact hheld⟩)

theorem collected_wellFormed {H H' : Heap Cell Owner} {o : Owner}
    (hw : H.WellFormed) (hc : Collected H H' o) : H'.WellFormed where
  staticClosed {c d} h hs := by
    have hnc := hc.not_owned (by rw [hs]; exact fun h' => by cases h')
    have hrc : H'.region c = H.region c := hc.region hnc
    have hH := hw.staticClosed ((hc.edges hnc).1 h) (hrc ▸ hs)
    have hnd : H.region d ≠ .owned o := by rw [hH]; exact fun h' => by cases h'
    rw [hc.region hnd, hH]
  epochClosed {c d e} h he := by
    have hnc := hc.not_owned (by rw [he]; exact fun h' => by cases h')
    have hrc : H'.region c = H.region c := hc.region hnc
    rcases hw.epochClosed ((hc.edges hnc).1 h) (hrc ▸ he) with hd | hd
    · have hnd : H.region d ≠ .owned o := by rw [hd]; exact fun h' => by cases h'
      exact Or.inl (by rw [hc.region hnd, hd])
    · have hnd : H.region d ≠ .owned o := by rw [hd]; exact fun h' => by cases h'
      exact Or.inr (by rw [hc.region hnd, hd])
  staticRoots {c} h := by
    have hs := hw.staticRoots (hc.staticRoot.1 h)
    have hnc : H.region c ≠ .owned o := by rw [hs]; exact fun h' => by cases h'
    rw [hc.region hnc, hs]
  slotsCurrent {c} h := by
    have hs := hw.slotsCurrent (hc.slot.1 h)
    have hnc : H.region c ≠ .owned o := by rw [hs]; exact fun h' => by cases h'
    rw [hc.region hnc, hs, hc.current]
  ownerRoots {o' c} hl h := by
    by_cases ho : o' = o
    · subst ho; exact hc.ownRoots h
    · exact hc.transfer ho (hw.ownerRoots (hc.live.1 hl) ((hc.otherRoots ho).1 h))
  ownedBounded {o' c d} h hco := by
    by_cases ho : o' = o
    · subst ho; exact hc.ownEdges h hco
    · have hnc := hc.not_owned (by rw [hco]; exact fun h' => by cases h'; exact ho rfl)
      have hrc : H'.region c = H.region c := hc.region hnc
      exact hc.transfer ho (hw.ownedBounded ((hc.edges hnc).1 h) (hrc ▸ hco))

/-- An owner's exit: it stops being live. -/
def exit (H : Heap Cell Owner) (o : Owner) : Heap Cell Owner :=
  { H with live := fun o' => H.live o' ∧ o' ≠ o }

theorem exit_wellFormed {H : Heap Cell Owner} (hw : H.WellFormed)
    (o : Owner) : (H.exit o).WellFormed where
  staticClosed := hw.staticClosed
  epochClosed := hw.epochClosed
  staticRoots := hw.staticRoots
  slotsCurrent := hw.slotsCurrent
  ownerRoots hl h := hw.ownerRoots hl.1 h
  ownedBounded := hw.ownedBounded

/-- A read: the owner `o` gains a root to the slot `s` and holds the current
epoch from then on. -/
def read (H : Heap Cell Owner) (o : Owner) (s : Cell) : Heap Cell Owner :=
  { H with
    ownerRoot := fun o' c => H.ownerRoot o' c ∨ (o' = o ∧ c = s)
    holds := fun o' e => H.holds o' e ∨ (o' = o ∧ e = H.current) }

theorem read_wellFormed {H : Heap Cell Owner} (hw : H.WellFormed)
    {o : Owner} {s : Cell} (hs : H.slot s) : (H.read o s).WellFormed := by
  have target : ∀ {o' c}, H.OwnerTarget o' c → (H.read o s).OwnerTarget o' c :=
    fun {o' c} ht => by
      rcases ht with h | h | ⟨e, he, hheld⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨e, he, Or.inl hheld⟩)
  exact
    { staticClosed := hw.staticClosed
      epochClosed := hw.epochClosed
      staticRoots := hw.staticRoots
      slotsCurrent := hw.slotsCurrent
      ownerRoots := fun {o' c} hl h => by
        rcases h with h | ⟨rfl, rfl⟩
        · exact target (hw.ownerRoots hl h)
        · exact Or.inr (Or.inr ⟨H.current, hw.slotsCurrent hs, Or.inr ⟨rfl, rfl⟩⟩)
      ownedBounded := fun h ho => target (hw.ownedBounded h ho) }

/-- A fresh cell: no edge, root or slot touches it yet. -/
structure Fresh (H : Heap Cell Owner) (n : Cell) : Prop where
  noOut : ∀ {d}, ¬ H.pointsTo n d
  noIn : ∀ {c}, ¬ H.pointsTo c n
  noStatic : ¬ H.staticRoot n
  noSlot : ¬ H.slot n
  noOwner : ∀ {o}, ¬ H.ownerRoot o n

/-- Allocate the fresh cell `n` in region `r` with children `kids`; `cached`
makes it a slot and `rooted` a static root. -/
def alloc [DecidableEq Cell] (H : Heap Cell Owner) (n : Cell) (r : Region Owner)
    (kids : Cell → Prop) (cached rooted : Prop) : Heap Cell Owner :=
  { H with
    region := fun c => if c = n then r else H.region c
    pointsTo := fun c d => H.pointsTo c d ∨ (c = n ∧ kids d)
    slot := fun c => H.slot c ∨ (c = n ∧ cached)
    staticRoot := fun c => H.staticRoot c ∨ (c = n ∧ rooted) }

theorem alloc_region_old [DecidableEq Cell] {H : Heap Cell Owner} {n c : Cell}
    {r : Region Owner} {kids : Cell → Prop} {cached rooted : Prop} (hc : c ≠ n) :
    (H.alloc n r kids cached rooted).region c = H.region c := by
  simp [alloc, hc]

theorem alloc_wellFormed [DecidableEq Cell] {H : Heap Cell Owner} (hw : H.WellFormed)
    {n : Cell} (hn : H.Fresh n) {r : Region Owner} {kids : Cell → Prop} {cached rooted : Prop}
    (hkid : ∀ {d}, kids d → d ≠ n)
    (hstatic : r = .static → ∀ {d}, kids d → H.region d = .static)
    (hepoch : ∀ {e}, r = .epoch e → ∀ {d}, kids d →
      H.region d = .epoch e ∨ H.region d = .static)
    (hcached : cached → r = .epoch H.current)
    (hrooted : rooted → r = .static)
    (howned : ∀ {o}, r = .owned o → ∀ {d}, kids d → H.OwnerTarget o d) :
    (H.alloc n r kids cached rooted).WellFormed := by
  have old : ∀ {c}, c ≠ n → (H.alloc n r kids cached rooted).region c = H.region c :=
    fun hc => alloc_region_old hc
  have edge_old : ∀ {c d}, H.pointsTo c d → c ≠ n ∧ d ≠ n := fun {c d} h =>
    ⟨fun hc => hn.noOut (hc ▸ h), fun hd => hn.noIn (hd ▸ h)⟩
  have target_old : ∀ {o d}, d ≠ n → H.OwnerTarget o d →
      (H.alloc n r kids cached rooted).OwnerTarget o d := fun {o d} hd ht => by
    unfold OwnerTarget at ht ⊢
    rw [old hd]
    simpa [alloc] using ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c d h hs
    rcases h with h | ⟨rfl, hk⟩
    · obtain ⟨hc, hd⟩ := edge_old h
      rw [old hc] at hs; rw [old hd]; exact hw.staticClosed h hs
    · have hr : r = .static := by simpa [alloc] using hs
      rw [old (hkid hk)]; exact hstatic hr hk
  · intro c d e h he
    rcases h with h | ⟨rfl, hk⟩
    · obtain ⟨hc, hd⟩ := edge_old h
      rw [old hc] at he; rw [old hd]; exact hw.epochClosed h he
    · have hr : r = .epoch e := by simpa [alloc] using he
      rw [old (hkid hk)]; exact hepoch hr hk
  · intro c h
    rcases h with h | ⟨rfl, hroot⟩
    · have hc : c ≠ n := fun hc => hn.noStatic (hc ▸ h)
      rw [old hc]; exact hw.staticRoots h
    · simpa [alloc] using hrooted hroot
  · intro c h
    rcases h with h | ⟨rfl, hcache⟩
    · have hc : c ≠ n := fun hc => hn.noSlot (hc ▸ h)
      rw [old hc]; exact hw.slotsCurrent h
    · simpa [alloc] using hcached hcache
  · intro o c hl h
    have hc : c ≠ n := fun hc => hn.noOwner (hc ▸ h)
    exact target_old hc (hw.ownerRoots hl h)
  · intro o c d h ho
    rcases h with h | ⟨rfl, hk⟩
    · obtain ⟨hc, hd⟩ := edge_old h
      rw [old hc] at ho
      exact target_old hd (hw.ownedBounded h ho)
    · have hr : r = .owned o := by simpa [alloc] using ho
      exact target_old (hkid hk) (howned hr hk)

/-- **Decoding**: a copy in the current epoch, its children decoded in the
same epoch or static, cached in a slot. -/
theorem decode_wellFormed [DecidableEq Cell] {H : Heap Cell Owner} (hw : H.WellFormed)
    {n : Cell} (hn : H.Fresh n) {kids : Cell → Prop} (hkid : ∀ {d}, kids d → d ≠ n)
    (hk : ∀ {d}, kids d → H.region d = .epoch H.current ∨ H.region d = .static) :
    (H.alloc n (.epoch H.current) kids True False).WellFormed :=
  alloc_wellFormed hw hn hkid (fun h => by cases h)
    (fun he _ hd => by cases he; exact hk hd) (fun _ => rfl) (fun h => h.elim)
    (fun h => by cases h)

/-- **Building static storage**: every child is static, because a store into
static storage copies a dynamic child first. -/
theorem buildStatic_wellFormed [DecidableEq Cell] {H : Heap Cell Owner} (hw : H.WellFormed)
    {n : Cell} (hn : H.Fresh n) {kids : Cell → Prop} {rooted : Prop}
    (hkid : ∀ {d}, kids d → d ≠ n) (hk : ∀ {d}, kids d → H.region d = .static) :
    (H.alloc n .static kids False rooted).WellFormed :=
  alloc_wellFormed hw hn hkid (fun _ _ hd => hk hd) (fun h => by cases h)
    (fun h => h.elim) (fun _ => rfl) (fun h => by cases h)

/-- **Building an owner's storage**: its children are what the owner may
point to; an export that copies the decoded copies it names is one. -/
theorem buildOwned_wellFormed [DecidableEq Cell] {H : Heap Cell Owner} (hw : H.WellFormed)
    {n : Cell} (hn : H.Fresh n) {o : Owner} {kids : Cell → Prop}
    (hkid : ∀ {d}, kids d → d ≠ n) (hk : ∀ {d}, kids d → H.OwnerTarget o d) :
    (H.alloc n (.owned o) kids False False).WellFormed :=
  alloc_wellFormed hw hn hkid (fun h => by cases h) (fun h => by cases h)
    (fun h => h.elim) (fun h => h.elim) (fun h _ hd => by cases h; exact hk hd)

/-- A static root that shares a decoded copy of epoch 0: no owner holds
epoch 0 and the current epoch is 1, yet the copy stays reachable. -/
def sharedCopy : Heap Bool Unit where
  region c := if c then .static else .epoch 0
  pointsTo c d := c = true ∧ d = false
  staticRoot c := c = true
  slot _ := False
  ownerRoot _ _ := False
  live _ := True
  current := 1
  holds _ _ := False

/-- **Without the copy rule, freeing is unsafe**: the shared copy's epoch is
freeable, yet reachable. -/
theorem shared_copy_resurrects : sharedCopy.Freeable 0 ∧ Reach sharedCopy.store false :=
  ⟨⟨by decide, fun _ _ h => h⟩, Reach.step (Reach.root (Or.inl rfl)) ⟨rfl, rfl⟩⟩

end Heap

end Mettapedia.GSLT.Dynamics.EpochReclamation
