import Mettapedia.Machines.ColumnPostingLayouts

/-!
# On-demand column indexes and nested-probe joins

Row IDs belong to one captured table. Distinct IDs retain duplicate payloads.
Index construction and retirement preserve every bound-column query; changing
the table starts with an empty cache. A nested-probe join is compared with an
independent relational product/filter specification. No logarithmic lookup,
rent bound, concurrent snapshot protocol or persistent-ID guarantee is inferred.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.IndexedTupleJoin

open ColumnPostingLayouts

variable {Id Value : Type} {k : Nat} [DecidableEq Id] [LinearOrder Value]

abbrev Tuple (k : Nat) (Value : Type) := Fin k → Value
abbrev Bounds (k : Nat) (Value : Type) := List (Fin k × Value)

structure Table (Id Value : Type) (k : Nat) where
  ids : List Id
  unique : ids.Nodup
  row : Id → Tuple k Value

inductive Layout (Id Value : Type) where
  | sorted (index : SortedColumn Value Id)
  | offset (index : OffsetColumn Value Id)
  | hashed (hash : Value → Nat) (index : HashedColumn Id)

inductive Kind where
  | sorted | offset | hashed
  deriving DecidableEq

def makeIndex (kind : Kind) (hash : Value → Nat) (t : Table Id Value k) (c : Fin k) : Layout Id Value :=
  match kind with
  | .sorted => .sorted (buildSorted t.ids (fun i => t.row i c))
  | .offset => .offset (buildOffset t.ids (fun i => t.row i c))
  | .hashed => .hashed hash (buildHashed t.ids (fun i => t.row i c) hash)

def readIndex (t : Table Id Value k) (c : Fin k) (index : Layout Id Value) (q : Value) : Finset Id :=
  match index with
  | .sorted index => lookupSorted index q
  | .offset index => lookupOffset index q
  | .hashed hash index => lookupHashed index (fun i => t.row i c) hash q

theorem read_makeIndex (kind : Kind) (hash : Value → Nat) (t : Table Id Value k)
    (c : Fin k) (q : Value) :
    readIndex t c (makeIndex kind hash t c) q = scan t.ids (fun i => t.row i c) q := by
  cases kind <;> simp [readIndex, makeIndex, lookupSorted_exact, lookupOffset_exact, lookupHashed_exact]

abbrev Cache (Id Value : Type) (k : Nat) := Fin k → Option (Layout Id Value)

def emptyCache : Cache Id Value k := fun _ => none

def Valid (t : Table Id Value k) (cache : Cache Id Value k) : Prop :=
  ∀ c index, cache c = some index → ∀ q, readIndex t c index q = scan t.ids (fun i => t.row i c) q

def build (kind : Kind) (hash : Value → Nat) (t : Table Id Value k) (c : Fin k)
    (cache : Cache Id Value k) : Cache Id Value k :=
  Function.update cache c (some (makeIndex kind hash t c))

def dropIndex (c : Fin k) (cache : Cache Id Value k) : Cache Id Value k := Function.update cache c none

theorem valid_empty (t : Table Id Value k) : Valid t emptyCache := by simp [Valid, emptyCache]

theorem valid_build (kind : Kind) (hash : Value → Nat) (t : Table Id Value k) (c : Fin k)
    (cache : Cache Id Value k) (valid : Valid t cache) : Valid t (build kind hash t c cache) := by
  intro d index found q
  by_cases hd : d = c
  · subst d
    simp only [build, Function.update_self, Option.some.injEq] at found
    subst index
    exact read_makeIndex kind hash t c q
  · exact valid d index (by simpa [build, Function.update_of_ne hd] using found) q

theorem valid_drop (t : Table Id Value k) (c : Fin k) (cache : Cache Id Value k)
    (valid : Valid t cache) : Valid t (dropIndex c cache) := by
  intro d index found q
  by_cases hd : d = c
  · subst d; simp [dropIndex] at found
  · exact valid d index (by simpa [dropIndex, Function.update_of_ne hd] using found) q

def selectColumn (t : Table Id Value k) (cache : Cache Id Value k) (c : Fin k) (q : Value) : Finset Id :=
  match cache c with
  | none => scan t.ids (fun i => t.row i c) q
  | some index => readIndex t c index q

theorem selectColumn_exact (t : Table Id Value k) (cache : Cache Id Value k)
    (valid : Valid t cache) (c : Fin k) (q : Value) :
    selectColumn t cache c q = scan t.ids (fun i => t.row i c) q := by
  cases found : cache c with
  | none => simp [selectColumn, found]
  | some index => simpa only [selectColumn, found] using valid c index found q

def acceptsBounds (bounds : Bounds k Value) (row : Tuple k Value) : Bool :=
  bounds.all (fun b => row b.1 == b.2)

def query (t : Table Id Value k) (cache : Cache Id Value k) : Bounds k Value → Finset Id
  | [] => t.ids.toFinset
  | (c, q) :: bounds => selectColumn t cache c q ∩ query t cache bounds

def reference (t : Table Id Value k) (bounds : Bounds k Value) : Finset Id :=
  t.ids.toFinset.filter (fun i => acceptsBounds bounds (t.row i) = true)

theorem mem_reference (t : Table Id Value k) (bounds : Bounds k Value) (i : Id) :
    i ∈ reference t bounds ↔ i ∈ t.ids ∧ acceptsBounds bounds (t.row i) = true := by
  simp only [reference, Finset.mem_filter, List.mem_toFinset]

theorem accepts_append (first second : Bounds k Value) (row : Tuple k Value) :
    acceptsBounds (first ++ second) row = (acceptsBounds first row && acceptsBounds second row) := by
  exact List.all_append

/-- Any set/list of bound columns, including contradictory repeated bounds. -/
theorem query_exact (t : Table Id Value k) (cache : Cache Id Value k) (valid : Valid t cache)
    (bounds : Bounds k Value) : query t cache bounds = reference t bounds := by
  induction bounds with
  | nil => simp [query, reference, acceptsBounds]
  | cons bound bounds ih =>
    rcases bound with ⟨c, q⟩
    ext i
    simp only [query, selectColumn_exact t cache valid, ih, Finset.mem_inter,
      scan, Finset.mem_filter, List.mem_toFinset, mem_reference]
    simp only [acceptsBounds, List.all_cons, Bool.and_eq_true, beq_iff_eq]
    tauto

theorem query_build (kind : Kind) (hash : Value → Nat) (t : Table Id Value k) (c : Fin k)
    (cache : Cache Id Value k) (valid : Valid t cache) (bounds : Bounds k Value) :
    query t (build kind hash t c cache) bounds = query t cache bounds := by
  rw [query_exact t _ (valid_build kind hash t c cache valid), query_exact t cache valid]

theorem query_drop (t : Table Id Value k) (c : Fin k) (cache : Cache Id Value k)
    (valid : Valid t cache) (bounds : Bounds k Value) :
    query t (dropIndex c cache) bounds = query t cache bounds := by
  rw [query_exact t _ (valid_drop t c cache valid), query_exact t cache valid]

inductive Maintenance (Value : Type) (k : Nat) where
  | build (column : Fin k) (kind : Kind) (hash : Value → Nat)
  | drop (column : Fin k)

def maintain (t : Table Id Value k) : List (Maintenance Value k) → Cache Id Value k → Cache Id Value k
  | [], cache => cache
  | .build c kind hash :: actions, cache => maintain t actions (build kind hash t c cache)
  | .drop c :: actions, cache => maintain t actions (dropIndex c cache)

theorem maintain_valid (t : Table Id Value k) (actions : List (Maintenance Value k))
    (cache : Cache Id Value k) (valid : Valid t cache) : Valid t (maintain t actions cache) := by
  induction actions generalizing cache with
  | nil => exact valid
  | cons action actions ih =>
    cases action with
    | build c kind hash => exact ih _ (valid_build kind hash t c cache valid)
    | drop c => exact ih _ (valid_drop t c cache valid)

/-- Any demand-driven build/drop schedule preserves the same captured-table answers. -/
theorem query_maintenance (t : Table Id Value k) (actions : List (Maintenance Value k))
    (cache : Cache Id Value k) (valid : Valid t cache) (bounds : Bounds k Value) :
    query t (maintain t actions cache) bounds = query t cache bounds := by
  rw [query_exact t _ (maintain_valid t actions cache valid), query_exact t cache valid]

def payloads (t : Table Id Value k) (hits : Finset Id) : Multiset (Tuple k Value) := hits.val.map t.row

/-- Equal tuple values at distinct row IDs remain repeated answers. -/
theorem payloads_exact (t : Table Id Value k) (cache : Cache Id Value k) (valid : Valid t cache)
    (bounds : Bounds k Value) :
    payloads t (query t cache bounds) =
      (t.ids.map t.row : Multiset (Tuple k Value)).filter (fun r => acceptsBounds bounds r = true) := by
  rw [query_exact t cache valid]
  have ids : t.ids.toFinset.val = (t.ids : Multiset Id) := by
    rw [List.toFinset_val, List.dedup_eq_self.mpr t.unique]
  simp only [payloads, reference, Finset.filter_val, ids]
  exact (Multiset.filter_map (fun row : Tuple k Value => acceptsBounds bounds row = true)
    t.row (t.ids : Multiset Id)).symm

theorem count_query_exact (t : Table Id Value k) (cache : Cache Id Value k) (valid : Valid t cache)
    (bounds : Bounds k Value) :
    (query t cache bounds).card =
      ((t.ids.map t.row : Multiset (Tuple k Value)).filter (fun row => acceptsBounds bounds row = true)).card := by
  have counted := congrArg Multiset.card (payloads_exact t cache valid bounds)
  simpa [payloads] using counted

variable {Right : Type} {r : Nat} [DecidableEq Right]

abbrev Links (k r : Nat) := List (Fin k × Fin r)

def linkBounds (links : Links k r) (left : Tuple k Value) : Bounds r Value :=
  links.map (fun p => (p.2, left p.1))

def agrees (links : Links k r) (left : Tuple k Value) (right : Tuple r Value) : Bool :=
  links.all (fun p => left p.1 == right p.2)

theorem accepts_linkBounds (links : Links k r) (left : Tuple k Value) (right : Tuple r Value) :
    acceptsBounds (linkBounds links left) right = agrees links left right := by
  simp only [acceptsBounds, linkBounds, agrees, List.all_map]
  apply congrArg (fun f : Fin k × Fin r → Bool => links.all f)
  funext p
  apply Bool.eq_iff_iff.mpr
  change (right p.2 == left p.1) = true ↔ (left p.1 == right p.2) = true
  constructor
  · intro h
    exact beq_iff_eq.mpr (beq_iff_eq.mp h).symm
  · intro h
    exact beq_iff_eq.mpr (beq_iff_eq.mp h).symm

theorem query_linkBounds (right : Table Right Value r) (cache : Cache Right Value r)
    (valid : Valid right cache) (bounds : Bounds r Value) (links : Links k r)
    (left : Tuple k Value) (j : Right) :
    j ∈ query right cache (bounds ++ linkBounds links left) ↔
      j ∈ reference right bounds ∧ agrees links left (right.row j) = true := by
  rw [query_exact right cache valid, mem_reference, mem_reference,
    accepts_append, accepts_linkBounds, Bool.and_eq_true]
  tauto

def nestedJoin (left : Table Id Value k) (right : Table Right Value r)
    (lc : Cache Id Value k) (rc : Cache Right Value r) (lb : Bounds k Value) (rb : Bounds r Value)
    (links : Links k r) : Finset (Id × Right) :=
  (query left lc lb).biUnion (fun i =>
    (query right rc (rb ++ linkBounds links (left.row i))).image (fun j => (i, j)))

def relationalJoin (left : Table Id Value k) (right : Table Right Value r)
    (lb : Bounds k Value) (rb : Bounds r Value) (links : Links k r) : Finset (Id × Right) :=
  ((reference left lb).product (reference right rb)).filter
    (fun p => agrees links (left.row p.1) (right.row p.2) = true)

/-- Nested column probes equal an independently filtered relational product. -/
theorem nestedJoin_exact (left : Table Id Value k) (right : Table Right Value r)
    (lc : Cache Id Value k) (rc : Cache Right Value r)
    (lv : Valid left lc) (rv : Valid right rc)
    (lb : Bounds k Value) (rb : Bounds r Value) (links : Links k r) :
    nestedJoin left right lc rc lb rb links = relationalJoin left right lb rb links := by
  ext pair
  rcases pair with ⟨i, j⟩
  rw [relationalJoin, Finset.mem_filter]
  simp only [nestedJoin, Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨i', hi, j', hj, rfl, rfl⟩
    rw [query_exact left lc lv] at hi
    obtain ⟨hj, linked⟩ := (query_linkBounds right rc rv rb links (left.row i') j').mp hj
    exact ⟨Finset.mem_product.mpr ⟨hi, hj⟩, linked⟩
  · rintro ⟨pairMember, linked⟩
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp pairMember
    refine ⟨i, ?_, j, ?_, rfl, rfl⟩
    · rwa [query_exact left lc lv]
    · exact (query_linkBounds right rc rv rb links (left.row i) j).mpr ⟨hj, linked⟩

def duplicateTable : Table Nat Nat 1 := ⟨[0, 1], by decide, fun _ _ => 7⟩

example : (payloads duplicateTable (query duplicateTable emptyCache [(0, 7)])).card = 2 := by decide
example : query duplicateTable emptyCache [(0, 7), (0, 8)] = ∅ := by decide
example : (nestedJoin duplicateTable duplicateTable emptyCache emptyCache [] [] [(0, 0)]).card = 4 := by decide

/-- A cache belongs to its captured table, not merely to a column number. -/
example :
    let old : Table Nat Nat 1 := ⟨[0], by decide, fun _ _ => 7⟩
    let changed : Table Nat Nat 1 := ⟨[0], by decide, fun _ _ => 8⟩
    let stale := build .offset id old 0 emptyCache
    query changed stale [(0, 8)] = ∅ ∧ reference changed [(0, 8)] = {0} := by decide

#print axioms query_exact
#print axioms query_build
#print axioms query_drop
#print axioms query_maintenance
#print axioms payloads_exact
#print axioms count_query_exact
#print axioms nestedJoin_exact

end Mettapedia.Machines.IndexedTupleJoin
