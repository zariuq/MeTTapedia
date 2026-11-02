import Mettapedia.Machines.CMemory.Fractional
import Mettapedia.Machines.CMemory.Borrowing
import Mathlib.Data.Finset.Basic

/-!+# State-indexed resources

The separation algebra describes compatibility, not authorization to change
the world. A memory update requires the whole permission. An authority change
leaves issued handles representable; a handle authorizes an effect only after
comparison with the current authority generation. Finite support bounds each
configuration without bounding the universe of allocation identities.

Allocation incarnations, revisions, authority generations, logical jobs and
transport attempts have distinct types. A C frontend may map its local block
numbers injectively into allocation identities; no numerical address is an
allocation identity in this interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Resources

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.Machines.CMemory
open scoped Mettapedia.GSLT.SeparationAlgebra

structure AllocationId where
  object : Nat
  incarnation : Nat
  deriving DecidableEq, Repr

structure Revision where
  number : Nat
  deriving DecidableEq, Repr

structure Generation where
  number : Nat
  deriving DecidableEq, Repr

structure JobId where
  owner : Nat
  number : Nat
  deriving DecidableEq, Repr

structure RequestId where
  caller : Nat
  number : Nat
  deriving DecidableEq, Repr

variable {K V : Type} [DecidableEq K]

/-- Finite support, rather than a finite universe of possible keys. -/
def FiniteSupport {R : Type} [Zero R] (r : K → R) : Prop :=
  ∃ keys : Finset K, ∀ k, k ∉ keys → r k = 0

theorem finiteSupport_update {R : Type} [Zero R] {r : K → R}
    (finite : FiniteSupport r) (key : K) (value : R) :
    FiniteSupport (Function.update r key value) := by
  obtain ⟨keys, outside⟩ := finite
  refine ⟨insert key keys, ?_⟩
  intro k absent
  have different : k ≠ key := fun same => absent (by simp [same])
  have rest : k ∉ keys := fun member => absent (Finset.mem_insert_of_mem member)
  simpa [different] using outside k rest

theorem finiteSupport_add {R : Type} [Zero R] [Add R] [SepAlgebra R]
    {r s : K → R} (finiteR : FiniteSupport r) (finiteS : FiniteSupport s) :
    FiniteSupport (r + s) := by
  obtain ⟨left, hl⟩ := finiteR
  obtain ⟨right, hr⟩ := finiteS
  refine ⟨left ∪ right, ?_⟩
  intro k absent
  have both := not_or.mp (fun h => absent (Finset.mem_union.mpr h))
  change r k + s k = 0
  rw [hl k both.1, hr k both.2, SepAlgebra.add_zero]

structure Cell (V : Type) where
  revision : Revision
  value : V
  deriving DecidableEq, Repr

abbrev Memory (V : Type) := AllocationId → Option (Cell V)
abbrev MemoryResource (V : Type) := AllocationId → Frac (Option (Cell V))

/-- Physical interpretation. A positive share observes the actual retained
cell. The share's amount is well formed independently of other holders. -/
def MemoryValid (world : Memory V) (r : MemoryResource V) : Prop :=
  FiniteSupport r ∧ ∀ key,
    match r key with
    | .none => True
    | .share amount _ observed => amount ≤ 1 ∧ world key = observed

def writeCell (world : Memory V) (key : AllocationId) (value : Cell V) : Memory V :=
  Function.update world key (some value)

def replacePermission (r : MemoryResource V) (key : AllocationId) (value : Cell V) :
    MemoryResource V := Function.update r key (CellPermission.whole (some value))

/-- An exclusive write changes a real cell, preserves every compatible
frame's physical interpretation, and remains compatible with that frame. -/
theorem write_preserves_frame {world : Memory V} {r frame : MemoryResource V}
    (valid : MemoryValid world r) (validFrame : MemoryValid world frame)
    (separate : r ## frame) (key : AllocationId) (old value : Cell V)
    (whole : r key = CellPermission.whole (some old)) :
    MemoryValid (writeCell world key value) (replacePermission r key value) ∧
    MemoryValid (writeCell world key value) frame ∧
    replacePermission r key value ## frame := by
  have empty : frame key = 0 :=
    CellPermission.eq_zero_of_whole_separate (by simpa [whole] using separate key)
  refine ⟨⟨finiteSupport_update valid.1 key _, ?_⟩, ⟨validFrame.1, ?_⟩, ?_⟩
  · intro k
    by_cases same : k = key
    · subst k
      simp [replacePermission, writeCell, CellPermission.whole]
    · simpa [replacePermission, writeCell, same] using valid.2 k
  · intro k
    by_cases same : k = key
    · subst k; simp [empty]
    · simpa [writeCell, same] using validFrame.2 k
  · intro k
    by_cases same : k = key
    · subst k; rw [empty]; exact SepAlgebra.separate_zero _
    · simpa [replacePermission, same] using separate k

theorem exclusive_excludes_positive_share (old other : Option (Cell V))
    (amount : ℚ) (positive : 0 < amount) :
    ¬ ((CellPermission.whole old : Frac (Option (Cell V))) ##
      Frac.share amount positive other) := by
  intro separate
  have empty := CellPermission.eq_zero_of_whole_separate separate
  cases empty

theorem halves_compatible (value : Option (Cell V)) :
    Frac.half value ## Frac.half value := (Frac.whole_eq_half_add_half value).1

/-- The root mapping is injective: reusing an address does not identify two
allocation incarnations or two distinct logical C allocation roots. -/
structure RootInterpretation where
  allocation : Nat → AllocationId
  injective : Function.Injective allocation

theorem interpreted_roots_distinct (mapping : RootInterpretation) {a b : Nat}
    (different : a ≠ b) : mapping.allocation a ≠ mapping.allocation b :=
  fun same => different (mapping.injective same)

structure Handle where
  principal : Nat
  resource : Nat
  generation : Generation
  deriving DecidableEq, Repr

structure Authority where
  generations : Nat → Generation
  issued : Finset Handle

def HandleValid (authority : Authority) (handle : Handle) : Prop := handle ∈ authority.issued

def MayAct (authority : Authority) (actor : Nat) (handle : Handle) : Prop :=
  HandleValid authority handle ∧ actor = handle.principal ∧
    authority.generations handle.resource = handle.generation

instance (authority : Authority) (actor : Nat) (handle : Handle) :
    Decidable (MayAct authority actor handle) :=
  inferInstanceAs (Decidable (handle ∈ authority.issued ∧ actor = handle.principal ∧
    authority.generations handle.resource = handle.generation))

/-- Revocation changes the authorization state, not the historical issuance
record or resources held by another party. -/
def revoke (authority : Authority) (resource : Nat) : Authority :=
  { authority with generations := Function.update authority.generations resource (Generation.mk ((authority.generations resource).number + 1)) }

theorem revoked_handle_still_representable (authority : Authority) (resource : Nat)
    (handle : Handle) (issued : HandleValid authority handle) :
    HandleValid (revoke authority resource) handle := issued

theorem revoke_blocks_old_action (authority : Authority) (actor : Nat) (handle : Handle)
    (current : authority.generations handle.resource = handle.generation) :
    ¬ MayAct (revoke authority handle.resource) actor handle := by
  rintro ⟨_, _, fresh⟩
  have impossible := congrArg Generation.number fresh
  simp [revoke, current] at impossible

theorem revoke_preserves_other_action (authority : Authority) (resource actor : Nat)
    (handle : Handle) (other : handle.resource ≠ resource) :
    MayAct (revoke authority resource) actor handle ↔ MayAct authority actor handle := by
  simp [MayAct, HandleValid, revoke, other]

/-- Representation validity of all outstanding issued handles is preserved;
no assertion that an old handle remains authorized is smuggled into framing. -/
theorem revoke_preserves_handle_frame (authority : Authority) (resource : Nat)
    (frame : Finset Handle) :
    (∀ handle ∈ frame, HandleValid (revoke authority resource) handle) ↔
      (∀ handle ∈ frame, HandleValid authority handle) := Iff.rfl

/-- Machine counters exhaust explicitly. No identity kind inherits the
reserved-value policy of another kind. -/
def nextCounter (maximum current : Nat) : Option Nat :=
  if current < maximum then some (current + 1) else none

theorem nextCounter_strict {maximum current next : Nat}
    (accepted : nextCounter maximum current = some next) : current < next ∧ next ≤ maximum := by
  unfold nextCounter at accepted
  split at accepted
  · cases Option.some.inj accepted; omega
  · cases accepted

theorem exhausted_counter (maximum current : Nat) (full : maximum ≤ current) :
    nextCounter maximum current = none := by
  simp [nextCounter, Nat.not_lt_of_ge full]

/-- Object ids reserve zero and the maximum value for other meanings. The
stored next-id may reach the maximum sentinel, but it may never be issued.
This differs from a transport counter whose last returned id may be maximum. -/
def issueObjectId (maximum current : Nat) : Option (Nat × Nat) :=
  if 0 < current then (nextCounter maximum current).map (fun next => (current, next)) else none

theorem issued_object_not_reserved {maximum current issued next : Nat}
    (accepted : issueObjectId maximum current = some (issued, next)) :
    0 < issued ∧ issued < maximum ∧ issued < next ∧ next ≤ maximum := by
  unfold issueObjectId at accepted
  split at accepted
  · rename_i positive
    cases increment : nextCounter maximum current with
    | none => simp [increment] at accepted
    | some n =>
      simp only [increment, Option.map_some, Option.some.injEq, Prod.mk.injEq] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      obtain ⟨strict, bounded⟩ := nextCounter_strict increment
      exact ⟨positive, lt_of_lt_of_le strict bounded, strict, bounded⟩
  · cases accepted

theorem object_maximum_not_issued (maximum : Nat) : issueObjectId maximum maximum = none := by
  simp [issueObjectId, exhausted_counter maximum maximum le_rfl]

theorem transport_and_object_reservations_differ :
    nextCounter 255 254 = some 255 ∧ issueObjectId 255 255 = none := by decide

#print axioms write_preserves_frame
#print axioms exclusive_excludes_positive_share
#print axioms revoke_blocks_old_action

end Mettapedia.Machines.Resources
