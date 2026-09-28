import Mettapedia.Machines.ResourceOwnership

/-!
# A resource sweep from indexed store roots

Some cells of a finite heap (`ResourceOwnership.Heap`) are *resources*: they
hold something the heap does not own, such as a foreign object or runtime
text, which the runtime releases explicitly.  Owners root addresses; at a safe
point between evaluation episodes only the stores' roots remain (spaces, the
registry, states, tables).

A store keeps an *index*: its roots whose footprint holds a resource
(`index`).  A sweep marks the resources the indexed roots reach and releases
every other resource.  Because a root outside the index reaches no resource,
the marks are exactly the resources the whole root set reaches
(`sweep_marks_iff`).  So the sweep agrees with `collect` on resources: a
resource that some root reaches keeps its cell (`sweep_keeps_live`), every
other resource leaves (`sweep_releases_dead`), and what is kept lies in the
roots' footprint (`marked_subset_footprint`).

The runtime computes the index with a summary bit folded over the children as
a term is constructed.  `summaryIndex_eq_index` shows that such a bit selects
exactly the index, given the fold law (a cell's bit is set exactly when it is
a resource or a reference of it has the bit set) on a heap without cycles.
Terms are built children first and never mutated, so their graph has no
cycles.

At an episode's end its roots are cancelled (`ResourceOwnership.cancel`); the
sweep then runs over the stores' roots alone (`sweep_after_close`).  This is a
sequential contract over one heap; it does not model concurrent mutators, and
enumerating every store's roots is the runtime's obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.IndexedResourceSweep

open Mettapedia.Machines.ResourceOwnership

universe uValue uOwner

variable {Address : Type} {Value : Type uValue} {Owner : Type uOwner}
variable [DecidableEq Address]

/-- The roots whose footprint holds a resource. -/
noncomputable def index (h : Heap Address Value) (isResource : Address → Prop)
    (roots : Roots Owner Address) : Roots Owner Address := by
  classical
  exact roots.filter (fun pair => ∃ a ∈ footprint h {pair}, isResource a)

/-- The resources a sweep from the index keeps. -/
noncomputable def marked (h : Heap Address Value) (isResource : Address → Prop)
    (roots : Roots Owner Address) : Finset Address := by
  classical
  exact (footprint h (index h isResource roots)).filter isResource

theorem index_subset (h : Heap Address Value) (isResource : Address → Prop)
    (roots : Roots Owner Address) : index h isResource roots ⊆ roots := by
  classical
  intro pair member
  exact (Finset.mem_filter.mp member).1

/-- A resource is reached from the index exactly when some root reaches it. -/
theorem sweep_marks_iff (h : Heap Address Value) (isResource : Address → Prop)
    (roots : Roots Owner Address) {a : Address} (resource : isResource a) :
    a ∈ footprint h (index h isResource roots) ↔ a ∈ footprint h roots := by
  classical
  constructor
  · exact fun member => footprint_mono h (index_subset h isResource roots) member
  · intro member
    rw [footprint_eq_biUnion] at member ⊢
    obtain ⟨pair, rooted, reached⟩ := Finset.mem_biUnion.mp member
    exact Finset.mem_biUnion.mpr
      ⟨pair, Finset.mem_filter.mpr ⟨rooted, a, reached, resource⟩, reached⟩

theorem mem_marked_iff (h : Heap Address Value) (isResource : Address → Prop)
    (roots : Roots Owner Address) (a : Address) :
    a ∈ marked h isResource roots ↔ isResource a ∧ Live h roots a := by
  classical
  simp only [marked, Finset.mem_filter]
  constructor
  · rintro ⟨reached, resource⟩
    exact ⟨resource, (mem_footprint h roots a).mp
      ((sweep_marks_iff h isResource roots resource).mp reached)⟩
  · rintro ⟨resource, live⟩
    exact ⟨(sweep_marks_iff h isResource roots resource).mpr
      ((mem_footprint h roots a).mpr live), resource⟩

/-- Survival: a resource some root reaches is kept, with its cell. -/
theorem sweep_keeps_live (h : Heap Address Value) (isResource : Address → Prop)
    (roots : Roots Owner Address) {a : Address} (resource : isResource a)
    (live : Live h roots a) :
    a ∈ marked h isResource roots ∧ (collect h roots).lookup a = h.lookup a :=
  ⟨(mem_marked_iff h isResource roots a).mpr ⟨resource, live⟩,
    lookup_collect_of_live h roots live⟩

/-- Reclamation: a resource no root reaches is released. -/
theorem sweep_releases_dead (h : Heap Address Value)
    (isResource : Address → Prop) (roots : Roots Owner Address) {a : Address}
    (dead : ¬ Live h roots a) :
    a ∉ marked h isResource roots ∧ (collect h roots).lookup a = none :=
  ⟨fun member => dead ((mem_marked_iff h isResource roots a).mp member).2,
    lookup_collect_of_not_live h roots dead⟩

/-- Bounded retention: the kept resources lie in the roots' footprint. -/
theorem marked_subset_footprint (h : Heap Address Value)
    (isResource : Address → Prop) (roots : Roots Owner Address) :
    marked h isResource roots ⊆ footprint h roots := by
  intro a member
  exact (mem_footprint h roots a).mpr
    ((mem_marked_iff h isResource roots a).mp member).2

/-- The kept resources are exactly the resources `collect` keeps. -/
theorem marked_eq_collect (h : Heap Address Value) (isResource : Address → Prop)
    [DecidablePred isResource] (roots : Roots Owner Address) :
    marked h isResource roots =
      (collect h roots).allocated.filter isResource := by
  classical
  ext a
  rw [mem_marked_iff, Finset.mem_filter, allocated_collect, mem_footprint]
  exact And.comm

/-- After an episode's owners are cancelled, the sweep keeps exactly the
resources the remaining owners reach. -/
theorem sweep_after_close [DecidableEq Owner] (h : Heap Address Value)
    (isResource : Address → Prop) (roots : Roots Owner Address)
    (episode : Finset Owner) (a : Address) :
    a ∈ marked h isResource (cancel roots episode) ↔
      isResource a ∧ Live h (cancel roots episode) a :=
  mem_marked_iff h isResource (cancel roots episode) a

/-! ## The index from a folded summary bit -/

/-- The fold law of a summary bit: a cell's bit is set exactly when it is a
resource or one of its references has the bit set. -/
def FoldLaw (h : Heap Address Value) (isResource : Address → Prop)
    (bit : Address → Prop) : Prop :=
  ∀ a c, h.lookup a = some c →
    (bit a ↔ isResource a ∨ ∃ b ∈ c.references, bit b)

/-- A heap without cycles: references decrease a rank. -/
def Ranked (h : Heap Address Value) (rank : Address → Nat) : Prop :=
  ∀ a c, h.lookup a = some c → ∀ b ∈ c.references, rank b < rank a

/-- The only root of a single root pair is its address. -/
theorem root_single_iff (h : Heap Address Value) (o : Owner) (x a : Address) :
    (h.toStore ({(o, x)} : Roots Owner Address)).root a ↔
      a ∈ h.allocated ∧ a = x := by
  simp [Heap.toStore, rootAddresses]

/-- Reachability from one root composes. -/
theorem live_single_trans (h : Heap Address Value) (o : Owner)
    {x y z : Address} (first : Live h ({(o, x)} : Roots Owner Address) y)
    (second : Live h ({(o, y)} : Roots Owner Address) z) :
    Live h ({(o, x)} : Roots Owner Address) z := by
  induction second with
  | @root a rooted =>
      have same : a = y := ((root_single_iff h o y a).mp rooted).2
      exact same ▸ first
  | @step a b _ edge ih =>
      obtain ⟨c, found, member⟩ := edge
      exact live_step h _ ih found member

/-- A bit reaches back up every path to the root. -/
theorem bit_of_live_bit (h : Heap Address Value) (isResource : Address → Prop)
    (bit : Address → Prop) (law : FoldLaw h isResource bit) (o : Owner)
    {x a : Address} (live : Live h ({(o, x)} : Roots Owner Address) a) :
    bit a → bit x := by
  induction live with
  | @root a rooted =>
      have same : a = x := ((root_single_iff h o x a).mp rooted).2
      exact fun set => same ▸ set
  | @step a b _ edge ih =>
      obtain ⟨c, found, member⟩ := edge
      intro set
      exact ih ((law a c found).mpr (Or.inr ⟨b, member, set⟩))

/-- The bit selects exactly the cells below which some resource lies. -/
theorem bit_iff_resource_below (h : Heap Address Value)
    (isResource : Address → Prop) (bit : Address → Prop)
    (law : FoldLaw h isResource bit) (rank : Address → Nat)
    (ranked : Ranked h rank) (o : Owner) {x : Address}
    (allocated : x ∈ h.allocated) :
    bit x ↔ ∃ r, Live h ({(o, x)} : Roots Owner Address) r ∧ isResource r := by
  constructor
  · -- Down the references, by the rank, to a resource.
    suffices descend : ∀ n a, rank a ≤ n → a ∈ h.allocated → bit a →
        ∃ r, Live h ({(o, a)} : Roots Owner Address) r ∧ isResource r from
      descend (rank x) x le_rfl allocated
    intro n
    induction n with
    | zero =>
        intro a small present set
        obtain ⟨c, found⟩ := (h.allocated_iff a).mp present
        rcases (law a c found).mp set with resource | ⟨b, member, _⟩
        · exact ⟨a, live_of_root h _ (owner := o) (by simp) present, resource⟩
        · have := ranked a c found b member
          omega
    | succ n ih =>
        intro a small present set
        obtain ⟨c, found⟩ := (h.allocated_iff a).mp present
        rcases (law a c found).mp set with resource | ⟨b, member, below⟩
        · exact ⟨a, live_of_root h _ (owner := o) (by simp) present, resource⟩
        · have lower : rank b ≤ n := by
            have := ranked a c found b member
            omega
          obtain ⟨r, reached, resource⟩ :=
            ih b lower (h.closed a c found b member) below
          have step : Live h ({(o, a)} : Roots Owner Address) b :=
            live_step h _ (live_of_root h _ (owner := o) (by simp) present)
              found member
          exact ⟨r, live_single_trans h o step reached, resource⟩
  · rintro ⟨r, reached, resource⟩
    obtain ⟨c, found⟩ :=
      (h.allocated_iff r).mp (live_allocated h _ reached)
    exact bit_of_live_bit h isResource bit law o reached
      ((law r c found).mpr (Or.inl resource))

/-- The roots whose summary bit is set. -/
noncomputable def summaryIndex (bit : Address → Prop)
    (roots : Roots Owner Address) : Roots Owner Address := by
  classical
  exact roots.filter (fun pair => bit pair.2)

/-- On a heap without cycles, a bit that obeys the fold law selects exactly the
index: the runtime's summary bit keeps the index the sweep needs. -/
theorem summaryIndex_eq_index (h : Heap Address Value)
    (isResource : Address → Prop) (bit : Address → Prop)
    (law : FoldLaw h isResource bit) (rank : Address → Nat)
    (ranked : Ranked h rank) (roots : Roots Owner Address)
    (valid : ValidRoots h roots) :
    summaryIndex bit roots = index h isResource roots := by
  classical
  ext pair
  simp only [summaryIndex, index, Finset.mem_filter, mem_footprint]
  constructor
  · rintro ⟨member, set⟩
    obtain ⟨r, reached, resource⟩ :=
      (bit_iff_resource_below h isResource bit law rank ranked pair.1
        (valid pair member)).mp set
    exact ⟨member, r, reached, resource⟩
  · rintro ⟨member, r, reached, resource⟩
    exact ⟨member, (bit_iff_resource_below h isResource bit law rank ranked
      pair.1 (valid pair member)).mpr ⟨r, reached, resource⟩⟩

end Mettapedia.Machines.IndexedResourceSweep
