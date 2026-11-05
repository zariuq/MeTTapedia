import Mettapedia.Machines.ResourceOwnership

/-!
# Reachability evidence through root retirement

A fixed graph admits a root-indexed reachability support. The ledger counts
distinct active root identities supporting an address, not graph paths or
native incoming references. Retiring an already retired identity has no effect;
retiring one of two roots with overlapping support does not erase the other.

The executable heap census constructs the supports. Incremental subtraction is
proved against independent inductive reachability, including cyclic heaps.
The graph and address identities remain fixed: root acquisition, graph writes,
resurrection and storage reset need separate admission. This is not a physical
collector or a discovery procedure for hidden foreign roots.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RootRetirementLedger

universe u v

variable {Root : Type u} {Address : Type v}
variable [DecidableEq Root] [DecidableEq Address]

/-- Root identities contributing at one address. -/
def contributors (support : Root → Finset Address) (active : Finset Root)
    (address : Address) : Finset Root :=
  active.filter fun root => address ∈ support root

structure Ledger (Root : Type u) (Address : Type v) where
  active : Finset Root
  support : Root → Finset Address
  count : Address → Nat

def Consistent (ledger : Ledger Root Address) : Prop :=
  ∀ address, ledger.count address = (contributors ledger.support ledger.active address).card

def prepare (support : Root → Finset Address) (active : Finset Root) : Ledger Root Address :=
  ⟨active, support, fun address => (contributors support active address).card⟩

omit [DecidableEq Root] in
theorem prepare_consistent (support : Root → Finset Address) (active : Finset Root) :
    Consistent (prepare support active) := fun _ => rfl

/-- Only currently active requested roots contribute a decrement. -/
def retire (ledger : Ledger Root Address) (requested : Finset Root) : Ledger Root Address :=
  { active := ledger.active \ requested
    support := ledger.support
    count := fun address => ledger.count address -
      (contributors ledger.support (ledger.active ∩ requested) address).card }

theorem contributors_sdiff (support : Root → Finset Address) (active requested : Finset Root)
    (address : Address) :
    contributors support (active \ requested) address =
      contributors support active address \ requested := by
  ext root
  simp only [contributors, Finset.mem_filter, Finset.mem_sdiff]
  tauto

theorem contributors_inter (support : Root → Finset Address) (active requested : Finset Root)
    (address : Address) :
    contributors support (active ∩ requested) address =
      contributors support active address ∩ requested := by
  ext root
  simp only [contributors, Finset.mem_filter, Finset.mem_inter]
  tauto

/-- Subtraction cannot underflow when the ledger and retirement domain agree. -/
theorem retirement_partition (ledger : Ledger Root Address) (consistent : Consistent ledger)
    (requested : Finset Root) (address : Address) :
    (contributors ledger.support (ledger.active \ requested) address).card +
      (contributors ledger.support (ledger.active ∩ requested) address).card =
        ledger.count address := by
  rw [consistent, contributors_sdiff, contributors_inter]
  exact Finset.card_sdiff_add_card_inter _ _

theorem retire_consistent (ledger : Ledger Root Address) (consistent : Consistent ledger)
    (requested : Finset Root) : Consistent (retire ledger requested) := by
  intro address
  have partition := retirement_partition ledger consistent requested address
  simp only [retire]
  omega

@[simp] theorem retire_idempotent (ledger : Ledger Root Address) (requested : Finset Root) :
    retire (retire ledger requested) requested = retire ledger requested := by
  have noRemoved : (ledger.active \ requested) ∩ requested = ∅ := by
    ext root
    simp
  have sameActive : (ledger.active \ requested) \ requested = ledger.active \ requested := by
    ext root
    simp
  simp [retire, noRemoved, sameActive, contributors]

/-- Ordered retirement batches may overlap, and their final meaning is their union. -/
theorem retire_comp (ledger : Ledger Root Address) (consistent : Consistent ledger)
    (first second : Finset Root) :
    retire (retire ledger first) second = retire ledger (first ∪ second) := by
  have sameActive : (ledger.active \ first) \ second = ledger.active \ (first ∪ second) := by
    ext root
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  have left := retire_consistent (retire ledger first) (retire_consistent ledger consistent first) second
  have right := retire_consistent ledger consistent (first ∪ second)
  have sameCount : (retire (retire ledger first) second).count =
      (retire ledger (first ∪ second)).count := by
    funext address
    rw [left address, right address]
    change (contributors ledger.support ((ledger.active \ first) \ second) address).card = _
    rw [sameActive]
    rfl
  cases ledger
  simp only [retire] at sameCount ⊢
  congr

def retireMany (ledger : Ledger Root Address) : List (Finset Root) → Ledger Root Address
  | [] => ledger
  | requested :: rest => retireMany (retire ledger requested) rest

theorem retireMany_consistent (ledger : Ledger Root Address) (consistent : Consistent ledger)
    (batches : List (Finset Root)) : Consistent (retireMany ledger batches) := by
  induction batches generalizing ledger with
  | nil => exact consistent
  | cons requested rest ih => exact ih _ (retire_consistent ledger consistent requested)

theorem retireMany_active_subset (ledger : Ledger Root Address) (batches : List (Finset Root)) :
    (retireMany ledger batches).active ⊆ ledger.active := by
  induction batches generalizing ledger with
  | nil => exact Finset.Subset.refl _
  | cons requested rest ih => exact (ih _).trans Finset.sdiff_subset

theorem retireMany_support (ledger : Ledger Root Address) (batches : List (Finset Root)) :
    (retireMany ledger batches).support = ledger.support := by
  induction batches generalizing ledger with
  | nil => rfl
  | cons requested rest ih => exact ih _

omit [DecidableEq Root] in
/-- A positive support count is equivalent to a live supporting root. -/
theorem count_positive_iff (ledger : Ledger Root Address) (consistent : Consistent ledger)
    (address : Address) :
    0 < ledger.count address ↔ ∃ root ∈ ledger.active, address ∈ ledger.support root := by
  rw [consistent, Finset.card_pos]
  simp [contributors, Finset.Nonempty]

namespace Heap

open ResourceOwnership

variable {Owner : Type u} {A : Type} {Value : Type v}
variable [DecidableEq Owner] [DecidableEq A]

def supports (heap : ResourceOwnership.Heap A Value) (root : Owner × A) : Finset A :=
  census heap {root}

def begin (heap : ResourceOwnership.Heap A Value) (roots : Roots Owner A) :
    Ledger (Owner × A) A := prepare (supports heap) roots

omit [DecidableEq Owner] in
theorem support_exact (heap : ResourceOwnership.Heap A Value) (root : Owner × A)
    (valid : root.2 ∈ heap.allocated) (address : A) :
    address ∈ supports heap root ↔ Live heap {root} address := by
  apply mem_census_iff_live
  intro pair member
  have equal := Finset.mem_singleton.mp member
  simpa [equal] using valid

omit [DecidableEq Owner] in
/-- Supports computed from the heap make the generic ledger exact for graph liveness. -/
theorem positive_iff_live (heap : ResourceOwnership.Heap A Value)
    (ledger : Ledger (Owner × A) A) (consistent : Consistent ledger)
    (computed : ledger.support = supports heap) (valid : ValidRoots heap ledger.active)
    (address : A) : 0 < ledger.count address ↔ Live heap ledger.active address := by
  rw [count_positive_iff ledger consistent, live_iff_root]
  constructor
  · rintro ⟨root, member, reachable⟩
    rw [computed] at reachable
    exact ⟨root, member, (support_exact heap root (valid root member) address).mp reachable⟩
  · rintro ⟨root, member, live⟩
    refine ⟨root, member, ?_⟩
    rw [computed]
    exact (support_exact heap root (valid root member) address).mpr live

theorem retired_positive_iff_live (heap : ResourceOwnership.Heap A Value)
    (roots requested : Roots Owner A) (valid : ValidRoots heap roots) (address : A) :
    0 < (retire (begin heap roots) requested).count address ↔
      Live heap (roots \ requested) address := by
  apply positive_iff_live heap _ (retire_consistent _ (prepare_consistent _ _) _) rfl
  intro root member
  exact valid root (Finset.mem_sdiff.mp member).1

theorem retired_many_positive_iff_live (heap : ResourceOwnership.Heap A Value)
    (roots : Roots Owner A) (batches : List (Roots Owner A))
    (valid : ValidRoots heap roots) (address : A) :
    0 < (retireMany (begin heap roots) batches).count address ↔
      Live heap (retireMany (begin heap roots) batches).active address := by
  apply positive_iff_live heap _ (retireMany_consistent _ (prepare_consistent _ _) _)
    (retireMany_support _ _) _ address
  intro root member
  exact valid root (retireMany_active_subset _ _ member)

/-- A lookup filtered by the updated count realizes semantic collection at
the current root domain. No old positive mark participates in this decision. -/
def lookup (heap : ResourceOwnership.Heap A Value) (ledger : Ledger (Owner × A) A)
    (address : A) : Option (Cell A Value) :=
  if 0 < ledger.count address then heap.lookup address else none

omit [DecidableEq Owner] in
theorem lookup_exact (heap : ResourceOwnership.Heap A Value)
    (ledger : Ledger (Owner × A) A) (consistent : Consistent ledger)
    (computed : ledger.support = supports heap) (valid : ValidRoots heap ledger.active)
    (address : A) : lookup heap ledger address = (collect heap ledger.active).lookup address := by
  classical
  have correct := positive_iff_live heap ledger consistent computed valid address
  simp only [lookup, collect, correct]

/-- Root retirement preserves old negative evidence, not old positive evidence. -/
theorem old_unmarked_stays_unreachable (heap : ResourceOwnership.Heap A Value)
    (roots requested : Roots Owner A) (address : A)
    (absent : ¬ Live heap roots address) : ¬ Live heap (roots \ requested) address :=
  fun live => absent (live_mono heap Finset.sdiff_subset live)

end Heap

/-- A current trace answer is distinct from a stale positive or unavailable answer. -/
inductive Decision where
  | keep | release | refresh | inconsistent
  deriving DecidableEq, Repr

def decideRelease (nativeCount : Nat) (currentTrace : Option Bool) : Decision :=
  if nativeCount > 0 then .keep else
    match currentTrace with
    | some false => .release
    | some true => .inconsistent
    | none => .refresh

def TraceSound (live : Prop) : Option Bool → Prop
  | none => True
  | some true => live
  | some false => ¬ live

theorem release_requires_current_absence (nativeCount : Nat) (evidence : Option Bool)
    (live : Prop) (sound : TraceSound live evidence)
    (released : decideRelease nativeCount evidence = .release) : ¬ live := by
  unfold decideRelease at released
  split at released
  · contradiction
  · cases evidence with
    | none => contradiction
    | some value => cases value <;> simp_all [TraceSound]

/-- A stale mark is not a positive current certificate. -/
def reuseAfterRetirement (oldMarked : Bool) : Option Bool :=
  if oldMarked then none else some false

theorem reuse_after_retirement_sound
    {Owner : Type u} {A : Type} {Value : Type v} [DecidableEq Owner] [DecidableEq A]
    (heap : ResourceOwnership.Heap A Value) (roots requested : ResourceOwnership.Roots Owner A)
    (address : A) (oldMarked : Bool)
    (oldExact : oldMarked = true ↔ ResourceOwnership.Live heap roots address) :
    TraceSound (ResourceOwnership.Live heap (roots \ requested) address)
      (reuseAfterRetirement oldMarked) := by
  cases oldMarked with
  | true => trivial
  | false =>
      apply Heap.old_unmarked_stays_unreachable heap roots requested address
      intro live
      exact Bool.false_ne_true (oldExact.mpr live)

end Mettapedia.Machines.RootRetirementLedger
