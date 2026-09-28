import Mettapedia.Machines.Cursor.OwnedLifecycle
import Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone

/-!
# Weak interning of immutable content in the owned resource heap

The finite cache is not a strong root. Marking uses only declared owners;
cache pruning removes references outside the marked footprint before their
addresses can be reused. Interning either reuses a sound cache entry or
installs one fresh leaf, then gives the returned address to an explicit owner.

The observable contract proved here is immutable content. Stable identity of
a live representative is preserved; eternal identity across reclamation is
not asserted. A dialect exposing stronger nominal identity needs a stronger
contract. The sequential algorithm also does not establish concurrent pinning,
allocator failure behavior, or nonwrapping native generation counters.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ResourceWeakInterning

open ResourceOwnership

variable {Owner Address Text : Type}
  [DecidableEq Owner] [DecidableEq Address] [DecidableEq Text]

abbrev Cache (Text Address : Type) := List (Text × Address)

def find (text : Text) : Cache Text Address → Option Address
  | [] => none
  | (content, address) :: rest => if text = content then some address else find text rest

def CacheValid (heap : Heap Address Text) (cache : Cache Text Address) : Prop :=
  ∀ text address, (text, address) ∈ cache →
    ∃ cell, heap.lookup address = some cell ∧ cell.value = text

def readContent (heap : Heap Address Text) (address : Address) : Option Text :=
  (heap.lookup address).map Cell.value

omit [DecidableEq Address] in
theorem find_mem (text : Text) (cache : Cache Text Address) (address : Address)
    (found : find text cache = some address) : (text, address) ∈ cache := by
  induction cache with
  | nil => simp [find] at found
  | cons pair rest ih =>
      rcases pair with ⟨content, stored⟩
      by_cases same : text = content
      · simp only [find, same, if_true, Option.some.injEq] at found
        simp [same, found]
      · simp only [find, same, if_false] at found
        exact List.mem_cons_of_mem _ (ih found)

omit [DecidableEq Address] in
theorem find_reads_content (heap : Heap Address Text) (cache : Cache Text Address)
    (valid : CacheValid heap cache) (text : Text) (address : Address)
    (found : find text cache = some address) : readContent heap address = some text := by
  obtain ⟨cell, lookup, content⟩ := valid text address (find_mem text cache address found)
  simp [readContent, lookup, content]

omit [DecidableEq Owner] [DecidableEq Address] [DecidableEq Text] in
theorem readContent_allocated (heap : Heap Address Text) (address : Address) (text : Text)
    (content : readContent heap address = some text) : address ∈ heap.allocated := by
  cases found : heap.lookup address with
  | none => simp [readContent, found] at content
  | some cell => exact (heap.allocated_iff address).mpr ⟨cell, found⟩

/-- Executable pruning given the collector's marked address set. -/
def prune (marked : Finset Address) (cache : Cache Text Address) : Cache Text Address :=
  cache.filter (fun entry => decide (entry.2 ∈ marked))

omit [DecidableEq Text] in
@[simp] theorem mem_prune (marked : Finset Address) (cache : Cache Text Address)
    (text : Text) (address : Address) :
    (text, address) ∈ prune marked cache ↔ (text, address) ∈ cache ∧ address ∈ marked := by
  simp [prune]

/-- Pruning dead entries does not disturb lookup of a live representative,
even when unrelated keys precede it in the cache. -/
theorem find_prune_preserves (marked : Finset Address) (cache : Cache Text Address)
    (text : Text) (address : Address) (found : find text cache = some address)
    (live : address ∈ marked) : find text (prune marked cache) = some address := by
  induction cache with
  | nil => simp [find] at found
  | cons pair rest ih =>
      rcases pair with ⟨content, stored⟩
      by_cases same : text = content
      · have addressSame : stored = address := by simpa [find, same] using found
        simp [prune, find, same, addressSame, live]
      · have restFound : find text rest = some address := by
          simpa [find, same] using found
        by_cases retained : stored ∈ marked <;>
          simpa [prune, find, same, retained] using ih restFound

omit [DecidableEq Owner] [DecidableEq Text] in
theorem prune_valid (heap : Heap Address Text) (roots : Roots Owner Address)
    (cache : Cache Text Address) (valid : CacheValid heap cache) :
    CacheValid (collect heap roots) (prune (footprint heap roots) cache) := by
  intro text address present
  rcases (mem_prune _ _ _ _).mp present with ⟨cached, marked⟩
  obtain ⟨cell, lookup, content⟩ := valid text address cached
  exact ⟨cell, (lookup_collect_of_live heap roots
    ((mem_footprint heap roots address).mp marked)).trans lookup, content⟩

omit [DecidableEq Owner] [DecidableEq Text] in
/-- Every live cached representative remains at exactly the same address;
every dead cached representative is removed regardless of its text key. -/
theorem prune_preserves_exactly_live (heap : Heap Address Text)
    (roots : Roots Owner Address) (cache : Cache Text Address)
    (text : Text) (address : Address) :
    (text, address) ∈ prune (footprint heap roots) cache ↔
      (text, address) ∈ cache ∧ Live heap roots address := by
  simp

structure State (Owner Address Text : Type) where
  heap : Heap Address Text
  roots : Roots Owner Address
  cache : Cache Text Address

/-- The cache is never added to `roots`. Pruning precedes any later reuse. -/
noncomputable def collectWeak (state : State Owner Address Text) :
    State Owner Address Text :=
  ⟨collect state.heap state.roots, state.roots,
    prune (footprint state.heap state.roots) state.cache⟩

omit [DecidableEq Owner] [DecidableEq Text] in
theorem collectWeak_cache_valid (state : State Owner Address Text)
    (valid : CacheValid state.heap state.cache) :
    CacheValid (collectWeak state).heap (collectWeak state).cache :=
  prune_valid state.heap state.roots state.cache valid

omit [DecidableEq Owner] [DecidableEq Text] in
theorem collectWeak_valid_roots (state : State Owner Address Text)
    (valid : ValidRoots state.heap state.roots) :
    ValidRoots (collectWeak state).heap (collectWeak state).roots := by
  intro pair member
  apply (mem_footprint state.heap state.roots pair.2).mpr
  exact live_of_root state.heap state.roots (owner := pair.1) member (valid pair member)

omit [DecidableEq Owner] [DecidableEq Text] in
/-- A cached but unowned resource is collectable. Cache membership does not
increase the heap's traced footprint. -/
theorem cache_does_not_keep_alive (state : State Owner Address Text) (address : Address)
    (unowned : ¬ Live state.heap state.roots address) :
    (collectWeak state).heap.lookup address = none ∧
      ∀ text, (text, address) ∉ (collectWeak state).cache := by
  refine ⟨lookup_collect_of_not_live _ _ unowned, ?_⟩
  intro text
  change (text, address) ∉ prune (footprint state.heap state.roots) state.cache
  simp [unowned]

omit [DecidableEq Owner] [DecidableEq Text] in
theorem owned_representative_survives (state : State Owner Address Text)
    (owner : Owner) (address : Address) (owned : (owner, address) ∈ state.roots)
    (allocated : address ∈ state.heap.allocated) :
    readContent (collectWeak state).heap address = readContent state.heap address := by
  simp only [readContent, collectWeak,
    lookup_collect_of_live state.heap state.roots
      (live_of_root state.heap state.roots owned allocated)]

omit [DecidableEq Text] in
/-- Escaping answers use the same ownership protocol as cursors. Publishing
an answer root before weak collection protects its complete reachable graph. -/
theorem escaped_representative_survives (state : State Owner Address Text)
    (output : Owner) (answers : List Address) (address : Address)
    (live : Live state.heap (Cursor.OwnedLifecycle.answerRoots output answers) address) :
    (collectWeak { state with roots :=
      Cursor.OwnedLifecycle.publish state.roots output answers }).heap.lookup address =
      state.heap.lookup address := by
  apply lookup_collect_of_live
  exact live_mono state.heap Finset.subset_union_right live

def textCell (text : Text) (bytes : Nat) : Cell Address Text := ⟨text, ∅, bytes⟩

/-- Install a leaf. Interning's freshness precondition prevents replacement of
an existing cell; explicit reuse is possible only after collection removes it. -/
def putLeaf (heap : Heap Address Text) (address : Address) (text : Text) (bytes : Nat) :
    Heap Address Text where
  lookup := Function.update heap.lookup address (some (textCell text bytes))
  allocated := insert address heap.allocated
  allocated_iff other := by
    by_cases same : other = address
    · subst other
      simp
    · simpa [same] using heap.allocated_iff other
  closed other cell found target referenced := by
    by_cases same : other = address
    · subst other
      simp only [Function.update_self, Option.some.injEq] at found
      subst cell
      simp [textCell] at referenced
    · have old : heap.lookup other = some cell := by simpa [same] using found
      exact Finset.mem_insert_of_mem (heap.closed other cell old target referenced)

omit [DecidableEq Text] in
@[simp] theorem putLeaf_at (heap : Heap Address Text) (address : Address)
    (text : Text) (bytes : Nat) :
    (putLeaf heap address text bytes).lookup address = some (textCell text bytes) := by
  simp [putLeaf]

omit [DecidableEq Text] in
theorem putLeaf_other (heap : Heap Address Text) (address other : Address)
    (text : Text) (bytes : Nat) (different : other ≠ address) :
    (putLeaf heap address text bytes).lookup other = heap.lookup other := by
  simp [putLeaf, different]

omit [DecidableEq Text] in
theorem putLeaf_preserves_cache (heap : Heap Address Text)
    (cache : Cache Text Address) (valid : CacheValid heap cache)
    (address : Address) (text : Text) (bytes : Nat)
    (fresh : address ∉ heap.allocated) :
    CacheValid (putLeaf heap address text bytes) cache := by
  intro oldText oldAddress cached
  obtain ⟨cell, lookup, content⟩ := valid oldText oldAddress cached
  have different : oldAddress ≠ address := by
    intro same
    exact fresh (same ▸ (heap.allocated_iff oldAddress).mpr ⟨cell, lookup⟩)
  exact ⟨cell, (putLeaf_other heap address oldAddress text bytes different).trans lookup, content⟩

/-- Cache hits preserve representatives. A miss creates one content leaf and
one weak-cache entry. Both paths explicitly root the returned value for its
caller; the cache alone supplies no lifetime. -/
def intern (state : State Owner Address Text) (owner : Owner)
    (text : Text) (bytes : Nat) (fresh : Address) : Address × State Owner Address Text :=
  match find text state.cache with
  | some address => (address, { state with roots := insert (owner, address) state.roots })
  | none => (fresh, ⟨putLeaf state.heap fresh text bytes,
      insert (owner, fresh) state.roots, (text, fresh) :: state.cache⟩)

theorem find_after_intern (state : State Owner Address Text) (owner : Owner)
    (text : Text) (bytes : Nat) (fresh : Address) :
    let result := intern state owner text bytes fresh
    find text result.2.cache = some result.1 := by
  cases found : find text state.cache <;> simp [intern, found, find]

/-- Strongly reachable cached content retains its physical representative
through collection and another intern operation. No fresh allocation occurs. -/
theorem live_hit_reused_after_collection (state : State Owner Address Text)
    (owner : Owner) (text : Text) (bytes : Nat) (fresh address : Address)
    (found : find text state.cache = some address)
    (live : Live state.heap state.roots address) :
    (intern (collectWeak state) owner text bytes fresh).1 = address := by
  have preserved := find_prune_preserves (footprint state.heap state.roots)
    state.cache text address found ((mem_footprint _ _ _).mpr live)
  simp only [intern, collectWeak, preserved]

/-- The cache algorithm is sound under a checkable heap/cache invariant and
allocator freshness on misses. A hit requires no spare address. -/
theorem intern_correct (state : State Owner Address Text) (owner : Owner)
    (text : Text) (bytes : Nat) (fresh : Address)
    (valid : CacheValid state.heap state.cache)
    (freshOnMiss : find text state.cache = none → fresh ∉ state.heap.allocated) :
    let result := intern state owner text bytes fresh
    readContent result.2.heap result.1 = some text ∧
      (owner, result.1) ∈ result.2.roots ∧
      CacheValid result.2.heap result.2.cache := by
  cases found : find text state.cache with
  | some address =>
      simp only [intern, found]
      exact ⟨find_reads_content _ _ valid text address found, Finset.mem_insert_self _ _, valid⟩
  | none =>
      simp only [intern, found]
      refine ⟨by simp [readContent, textCell], Finset.mem_insert_self _ _, ?_⟩
      intro oldText oldAddress present
      rcases List.mem_cons.mp present with same | retained
      · have textSame : oldText = text := congrArg Prod.fst same
        have addressSame : oldAddress = fresh := congrArg Prod.snd same
        subst oldText
        subst oldAddress
        exact ⟨textCell text bytes, putLeaf_at _ _ _ _, rfl⟩
      · exact putLeaf_preserves_cache state.heap state.cache valid fresh text bytes
          (freshOnMiss found) oldText oldAddress retained

theorem intern_valid_roots (state : State Owner Address Text) (owner : Owner)
    (text : Text) (bytes : Nat) (fresh : Address)
    (cacheValid : CacheValid state.heap state.cache)
    (rootsValid : ValidRoots state.heap state.roots) :
    let result := intern state owner text bytes fresh
    ValidRoots result.2.heap result.2.roots := by
  cases found : find text state.cache with
  | some address =>
      simp only [intern, found]
      intro pair present
      rcases Finset.mem_insert.mp present with same | old
      · subst pair
        exact readContent_allocated state.heap address text
          (find_reads_content state.heap state.cache cacheValid text address found)
      · exact rootsValid pair old
  | none =>
      simp only [intern, found]
      intro pair present
      change pair.2 ∈ insert fresh state.heap.allocated
      rcases Finset.mem_insert.mp present with same | old
      · subst pair
        exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (rootsValid pair old)

/-- End-to-end lifetime law: the root returned by either intern path keeps
the requested text alive through weak-cache collection. -/
theorem intern_collect_content (state : State Owner Address Text) (owner : Owner)
    (text : Text) (bytes : Nat) (fresh : Address)
    (valid : CacheValid state.heap state.cache)
    (freshOnMiss : find text state.cache = none → fresh ∉ state.heap.allocated) :
    let result := intern state owner text bytes fresh
    readContent (collectWeak result.2).heap result.1 = some text := by
  have correct := intern_correct state owner text bytes fresh valid freshOnMiss
  exact (owned_representative_survives _ owner _ correct.2.1
    (readContent_allocated _ _ _ correct.1)).trans correct.1

/-- As long as the returned owner's root remains, reinterning after a
collection returns precisely the first representative, not just equal bytes. -/
theorem intern_collect_reuses (state : State Owner Address Text) (owner : Owner)
    (text : Text) (bytes : Nat) (fresh nextFresh : Address)
    (valid : CacheValid state.heap state.cache)
    (freshOnMiss : find text state.cache = none → fresh ∉ state.heap.allocated) :
    let result := intern state owner text bytes fresh
    (intern (collectWeak result.2) owner text bytes nextFresh).1 = result.1 := by
  have correct := intern_correct state owner text bytes fresh valid freshOnMiss
  apply live_hit_reused_after_collection _ owner text bytes nextFresh _
    (find_after_intern state owner text bytes fresh)
  exact live_of_root _ _ correct.2.1 (readContent_allocated _ _ _ correct.1)

/-- Reinterning can use different physical representatives while retaining
exact immutable content. This theorem makes no nominal-identity claim. -/
theorem reintern_content_equal (first second : State Owner Address Text) (owner : Owner)
    (text : Text) (bytes : Nat) (firstFresh secondFresh : Address)
    (firstValid : CacheValid first.heap first.cache)
    (secondValid : CacheValid second.heap second.cache)
    (firstAvailable : find text first.cache = none → firstFresh ∉ first.heap.allocated)
    (secondAvailable : find text second.cache = none → secondFresh ∉ second.heap.allocated) :
    let left := intern first owner text bytes firstFresh
    let right := intern second owner text bytes secondFresh
    readContent left.2.heap left.1 = readContent right.2.heap right.1 := by
  exact (intern_correct first owner text bytes firstFresh firstValid firstAvailable).1.trans
    (intern_correct second owner text bytes secondFresh secondValid secondAvailable).1.symm

omit [DecidableEq Owner] [DecidableEq Text] in
/-- The exact marking law rules out keeping dead representatives merely
because their key remains present in the intern table. -/
theorem no_roots_no_marked_cells (heap : Heap Address Text) :
    footprint heap (∅ : Roots Owner Address) = ∅ := by
  ext address
  simp [not_live_empty]

omit [DecidableEq Owner] [DecidableEq Text] in
theorem prune_empty (cache : Cache Text Address) : prune ∅ cache = [] := by
  simp [prune]

omit [DecidableEq Owner] [DecidableEq Text] in
theorem release_all_clears_cache (state : State Owner Address Text) :
    (collectWeak { state with roots := (∅ : Roots Owner Address) }).cache = [] := by
  simp only [collectWeak, no_roots_no_marked_cells, prune_empty]

omit [DecidableEq Owner] [DecidableEq Text] in
theorem release_all_frees_cells (state : State Owner Address Text) :
    (collectWeak { state with roots := (∅ : Roots Owner Address) }).heap.allocated = ∅ := by
  exact no_roots_no_marked_cells state.heap

open Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone (Handle)

/-- Internal validation for a generation-bearing external handle. Returning
`none` here is a failed lookup, not a chosen public language error policy. -/
def checkedContent (heap : Heap Address Text) (generation : Address → Nat)
    (handle : Handle Unit Address) : Option Text :=
  if generation handle.resource = handle.generation then
    readContent heap handle.resource else none

omit [DecidableEq Owner] [DecidableEq Address] [DecidableEq Text] in
theorem stale_generation_rejected (heap : Heap Address Text) (generation : Address → Nat)
    (handle : Handle Unit Address)
    (stale : generation handle.resource ≠ handle.generation) :
    checkedContent heap generation handle = none := by
  simp [checkedContent, stale]

/-- Payload spelling and dialect sort are independent observable data.
Interning may not identify a PeTTa symbol with an HE string of equal bytes. -/
inductive TextSort where
  | symbol
  | string
  deriving DecidableEq, Repr

structure SortedText where
  sort : TextSort
  content : String
  deriving DecidableEq, Repr

theorem intern_preserves_sort (state : State Owner Address SortedText) (owner : Owner)
    (text : SortedText) (bytes : Nat) (fresh : Address)
    (valid : CacheValid state.heap state.cache)
    (freshOnMiss : find text state.cache = none → fresh ∉ state.heap.allocated) :
    let result := intern state owner text bytes fresh
    (readContent result.2.heap result.1).map SortedText.sort = some text.sort := by
  dsimp only
  rw [(intern_correct state owner text bytes fresh valid freshOnMiss).1]
  rfl

namespace Controls

def emptyHeap : Heap Nat Text where
  lookup _ := none
  allocated := ∅
  allocated_iff _ := by simp
  closed _ _ impossible := by cases impossible

def empty : State Nat Nat Text := ⟨emptyHeap, ∅, []⟩

omit [DecidableEq Text] in
theorem empty_cache_valid : CacheValid (empty (Text := Text)).heap empty.cache := by
  intro text address impossible
  cases impossible

def first (text : String) : State Nat Nat String :=
  (intern empty 0 text 8 0).2

theorem first_cache_valid (text : String) : CacheValid (first text).heap (first text).cache := by
  exact (intern_correct empty 0 text 8 0 empty_cache_valid (by simp [empty, emptyHeap])).2.2

noncomputable def dropped (text : String) : State Nat Nat String :=
  collectWeak { first text with roots := ∅ }

theorem dropped_cache (text : String) : (dropped text).cache = [] :=
  release_all_clears_cache (first text)

theorem dropped_allocated (text : String) : (dropped text).heap.allocated = ∅ :=
  release_all_frees_cells (first text)

theorem dropped_valid (text : String) :
    CacheValid (dropped text).heap (dropped text).cache := by
  exact collectWeak_cache_valid { first text with roots := ∅ } (first_cache_valid text)

/-- An actual collect/prune/reintern sequence can change the address while
preserving content. Strong lifetime identity is not inferred from this law. -/
theorem reintern_can_change_identity :
    (intern empty 0 "same" 8 0).1 = 0 ∧
    (intern (dropped "same") 0 "same" 8 1).1 = 1 ∧
    readContent (first "same").heap 0 = some "same" ∧
    readContent (intern (dropped "same") 0 "same" 8 1).2.heap
      (intern (dropped "same") 0 "same" 8 1).1 = some "same" := by
  refine ⟨rfl, ?_, rfl, ?_⟩
  · simp [intern, dropped_cache, find]
  · exact (intern_correct (dropped "same") 0 "same" 8 1 (dropped_valid "same")
      (by intro _; simp [dropped_allocated])).1

/-- Reusing a freed address for different content is legal. Reading an old
unowned raw address then reads the new resource, not the old text. -/
theorem unowned_raw_address_is_stale :
    (intern (dropped "old") 1 "new" 8 0).1 = 0 ∧
    readContent (intern (dropped "old") 1 "new" 8 0).2.heap 0 = some "new" ∧
    checkedContent (intern (dropped "old") 1 "new" 8 0).2.heap
      (fun _ => 1) ⟨(), 0, 0⟩ = none := by
  have address : (intern (dropped "old") 1 "new" 8 0).1 = 0 := by
    simp [intern, dropped_cache, find]
  refine ⟨address, ?_, ?_⟩
  · have content := (intern_correct (dropped "old") 1 "new" 8 0 (dropped_valid "old")
        (by intro _; simp [dropped_allocated])).1
    simpa only [address] using content
  · exact stale_generation_rejected _ _ _ (by decide)

/-- This intentionally incorrect sweep keeps the stale cache entry while
making its address available for reuse. -/
noncomputable def unpruned : State Nat Nat String :=
  { dropped "old" with cache := (first "old").cache }

/-- Negative control: after reuse, a stale cache hit for the old key returns
the new text. Purging before reuse is required for this unchecked fast path. -/
theorem stale_cache_corrupts_content :
    let reused := (intern unpruned 1 "new" 8 0).2
    let wrong := intern reused 2 "old" 8 1
    readContent wrong.2.heap wrong.1 = some "new" ∧
      readContent wrong.2.heap wrong.1 ≠ some "old" := by
  simp [intern, unpruned, first, empty, find, readContent, putLeaf, textCell]

theorem same_bytes_different_sorts :
    let symbol : SortedText := ⟨.symbol, "hello"⟩
    let string : SortedText := ⟨.string, "hello"⟩
    let symbolResult := intern empty 0 symbol 8 0
    let stringResult := intern symbolResult.2 0 string 8 1
    symbolResult.1 ≠ stringResult.1 ∧
      readContent stringResult.2.heap symbolResult.1 = some symbol ∧
      readContent stringResult.2.heap stringResult.1 = some string := by
  decide

end Controls

#print axioms prune_valid
#print axioms cache_does_not_keep_alive
#print axioms escaped_representative_survives
#print axioms intern_correct
#print axioms intern_collect_content
#print axioms intern_collect_reuses
#print axioms intern_valid_roots
#print axioms reintern_content_equal
#print axioms Controls.reintern_can_change_identity
#print axioms Controls.unowned_raw_address_is_stale
#print axioms Controls.stale_cache_corrupts_content
#print axioms Controls.same_bytes_different_sorts

end Mettapedia.Machines.ResourceWeakInterning
