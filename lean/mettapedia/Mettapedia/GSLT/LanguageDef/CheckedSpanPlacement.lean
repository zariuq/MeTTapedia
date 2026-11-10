import Mettapedia.GSLT.LanguageDef.CheckedScalarSpans

/-!
# From live span permissions to machine address ranges

The allocation table is a caller-supplied interpretation, not a runtime borrow
ledger. Its entries describe live initialized storage. Logical roots, allocation
incarnations and numerical addresses remain distinct. Permission admission can
prove exclusive access; this interpretation is what connects that fact to
physical non-overlap. Compiler code/stack separation is an additional ABI duty.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CheckedSpanPlacement

open CheckedScalarSpans

/-- Declarative entry obligations. They are checked against emitted interface
evidence independently of the C emitter. They do not assert that a native
caller has discharged the live-storage interpretation. -/
structure EntryContract where
  spans : List (Nat × Element × CheckedBytes.Kind × Nat)
  separate : List (Nat × Nat)
  borrowedFrom : Option Nat
  deriving DecidableEq, Repr

def entryContract (wordBytes : Nat) (signature : Signature) : EntryContract :=
  let spans := signature.params.zipIdx.filterMap fun (slot, id) =>
    match slot with
    | .span element kind => some (id, element, kind, element.bytes wordBytes)
    | .scalar _ => none
  ⟨spans, spans.flatMap (fun (i, _, kind, _) =>
    spans.filterMap (fun (j, _, other, _) =>
      if i < j ∧ (kind.writable = true ∨ other.writable = true) then some (i, j) else none)),
    signature.sourceParameter⟩

structure Allocation where
  root : Nat
  incarnation : Nat
  base : Nat
  bytes : Nat
  initialized : Nat
  deriving DecidableEq, Repr

structure View where
  binding : CheckedBytes.Binding
  incarnation : Nat
  element : Element
  offset : Nat
  count : Nat
  alignment : Nat
  deriving DecidableEq, Repr

structure Span where
  address : Nat
  count : Nat
  stride : Nat
  deriving DecidableEq, Repr

def Span.bytes (s : Span) : Nat := s.count * s.stride

def Apart (a sizeA b sizeB : Nat) : Prop := a + sizeA ≤ b ∨ b + sizeB ≤ a

def TableValid (limit : Nat) (table : List Allocation) : Prop :=
  (table.map Allocation.root).Nodup ∧
  (∀ a ∈ table, a.initialized ≤ a.bytes ∧ a.base + a.bytes ≤ limit ∧
    (a.bytes ≠ 0 → a.base ≠ 0)) ∧
  ∀ a ∈ table, ∀ b ∈ table, a.root ≠ b.root → Apart a.base a.bytes b.base b.bytes

instance (a n b m : Nat) : Decidable (Apart a n b m) := inferInstanceAs (Decidable (_ ∨ _))
instance (limit : Nat) (table : List Allocation) : Decidable (TableValid limit table) := by
  unfold TableValid
  infer_instance

def resolve (wordBytes countByteLimit : Nat) (a : Allocation) (v : View) : Option Span := do
  let size ← allocationBytes (v.element.bytes wordBytes) countByteLimit v.count
  if v.binding.root = a.root ∧ v.incarnation = a.incarnation ∧
      v.offset * v.element.bytes wordBytes + size ≤ a.initialized ∧
      0 < v.alignment ∧ (a.base + v.offset * v.element.bytes wordBytes) % v.alignment = 0 ∧
      a.base + v.offset * v.element.bytes wordBytes < 2 ^ (8 * wordBytes)
  then some ⟨a.base + v.offset * v.element.bytes wordBytes, v.count, v.element.bytes wordBytes⟩
  else none

def resolveHeld (wordBytes countByteLimit : Nat) (table : List Allocation) (v : View) : Option Span :=
  (table.find? (fun a => a.root == v.binding.root)).bind fun a => resolve wordBytes countByteLimit a v

theorem resolve_facts {wordBytes countByteLimit : Nat} {a : Allocation} {v : View} {s : Span}
    (resolved : resolve wordBytes countByteLimit a v = some s) :
    v.binding.root = a.root ∧ v.incarnation = a.incarnation ∧
    s.address = a.base + v.offset * v.element.bytes wordBytes ∧
    s.count = v.count ∧ s.stride = v.element.bytes wordBytes ∧
    0 < s.stride ∧ s.bytes ≤ countByteLimit ∧
    s.address + s.bytes ≤ a.base + a.initialized ∧
    0 < v.alignment ∧ s.address % v.alignment = 0 ∧ s.address < 2 ^ (8 * wordBytes) := by
  obtain ⟨size, allocated, rest⟩ := Option.bind_eq_some_iff.mp resolved
  obtain ⟨sameSize, bounded, positive⟩ := allocationBytes_exact allocated
  split at rest
  next conditions =>
    cases Option.some.inj rest
    rcases conditions with ⟨root, incarnation, extent, alignment, aligned, addressBound⟩
    dsimp [Span.bytes]
    refine ⟨root, incarnation, rfl, rfl, rfl, positive, ?_, ?_, alignment, aligned, addressBound⟩
    · simpa [sameSize] using bounded
    · rw [sameSize] at extent
      omega
  next => cases rest

theorem held_allocation {wordBytes countByteLimit : Nat} {table : List Allocation} {v : View} {s : Span}
    (resolved : resolveHeld wordBytes countByteLimit table v = some s) :
    ∃ a ∈ table, resolve wordBytes countByteLimit a v = some s := by
  obtain ⟨a, found, resolved⟩ := Option.bind_eq_some_iff.mp resolved
  exact ⟨a, List.mem_of_find?_eq_some found, resolved⟩

theorem resolved_machine_bounds {wordBytes countByteLimit limit : Nat}
    {table : List Allocation} {v : View} {s : Span}
    (valid : TableValid limit table)
    (resolved : resolveHeld wordBytes countByteLimit table v = some s) :
    s.address + s.bytes ≤ limit ∧ s.bytes ≤ countByteLimit ∧
      (s.count ≠ 0 → s.address ≠ 0) ∧ s.address % v.alignment = 0 := by
  obtain ⟨a, present, placed⟩ := held_allocation resolved
  obtain ⟨_, _, address, count, stride, positive, size, extent, _, aligned, _⟩ := resolve_facts placed
  obtain ⟨initialized, fits, nonnull⟩ := valid.2.1 a present
  refine ⟨by omega, size, ?_, aligned⟩
  intro nonempty zero
  have product : 0 < s.bytes := Nat.mul_pos (Nat.pos_of_ne_zero nonempty) positive
  have baseZero : a.base = 0 := by omega
  have bytesPositive : a.bytes ≠ 0 := by omega
  exact nonnull bytesPositive baseZero

theorem different_roots_apart {wordBytes countByteLimit limit : Nat}
    {table : List Allocation} {a b : View} {x y : Span}
    (valid : TableValid limit table) (different : a.binding.root ≠ b.binding.root)
    (first : resolveHeld wordBytes countByteLimit table a = some x)
    (second : resolveHeld wordBytes countByteLimit table b = some y) :
    Apart x.address x.bytes y.address y.bytes := by
  obtain ⟨aa, ma, ra⟩ := held_allocation first
  obtain ⟨ab, mb, rb⟩ := held_allocation second
  obtain ⟨rootA, _, addressA, _, _, _, _, extentA, _⟩ := resolve_facts ra
  obtain ⟨rootB, _, addressB, _, _, _, _, extentB, _⟩ := resolve_facts rb
  have ia := (valid.2.1 aa ma).1
  have ib := (valid.2.1 ab mb).1
  have apart := valid.2.2 aa ma ab mb (by simpa [← rootA, ← rootB] using different)
  unfold Apart at apart ⊢
  rcases apart with before | after
  · left; omega
  · right; omega

/-- This is the permission-to-address step: physical non-aliasing follows from
two usable permissions and the placement interpretation, not from different
variable names or pointer inequality. Suspended parents cannot satisfy access. -/
theorem usable_writer_apart {wordBytes countByteLimit limit : Nat}
    {table : List Allocation} {state : CheckedBytes.State} {writer reader : View}
    {x y : Span} {reading : Bool}
    (permissions : CheckedBytes.Valid state) (placement : TableValid limit table)
    (write : CheckedBytes.CanAccess state writer.binding true)
    (read : CheckedBytes.CanAccess state reader.binding reading)
    (different : writer.binding.id ≠ reader.binding.id)
    (first : resolveHeld wordBytes countByteLimit table writer = some x)
    (second : resolveHeld wordBytes countByteLimit table reader = some y) :
    Apart x.address x.bytes y.address y.bytes := by
  apply different_roots_apart placement _ first second
  intro same
  exact different (CheckedBytes.exclusive_access permissions write read same)

/-- Composition at an intermediate point of the actual permission plan, while
its views are still live. Return cleanup may have discharged all of them. -/
theorem admitted_prefix_writer_apart {environment : List Signature} {f : Function}
    {reached : State}
    {wordBytes countByteLimit limit : Nat} {table : List Allocation}
    {writer reader : View} {x y : Span} {reading : Bool}
    (admitted : checkFunction environment f = true)
    (path : Mettapedia.Machines.CMemory.PermissionFlow.Prefix
      (transition environment f.signature) f.body (initial f.signature) reached)
    (placement : TableValid limit table)
    (write : CheckedBytes.CanAccess reached.permissions writer.binding true)
    (read : CheckedBytes.CanAccess reached.permissions reader.binding reading)
    (different : writer.binding.id ≠ reader.binding.id)
    (first : resolveHeld wordBytes countByteLimit table writer = some x)
    (second : resolveHeld wordBytes countByteLimit table reader = some y) :
    Apart x.address x.bytes y.address y.bytes := by
  unfold checkFunction at admitted
  obtain ⟨_, _, _, valid, _⟩ := (by simpa only [Bool.and_eq_true, and_assoc] using admitted)
  have initialValid : Valid (initial f.signature) := by simpa using valid
  have reachedValid := path.invariant (fun _ _ _ step _ => transition_valid step) initialValid
  exact usable_writer_apart reachedValid.1 placement write read different first second

theorem element_access_within {limit : Nat} {s : Span} {index : Nat}
    (bounded : s.address + s.bytes ≤ limit) (inside : index < s.count) :
    s.address + index * s.stride + s.stride ≤ limit := by
  have extent := Nat.mul_le_mul_right s.stride (Nat.succ_le_of_lt inside)
  simp only [Nat.succ_mul] at extent
  dsimp [Span.bytes] at bounded
  omega

theorem stale_incarnation_refused {wordBytes countByteLimit : Nat} {a : Allocation} {v : View}
    (stale : v.incarnation ≠ a.incarnation) : resolve wordBytes countByteLimit a v = none := by
  unfold resolve
  cases allocationBytes (v.element.bytes wordBytes) countByteLimit v.count <;> simp [stale]

theorem missing_root_refused (wordBytes countByteLimit : Nat) (v : View) :
    resolveHeld wordBytes countByteLimit [] v = none := rfl

namespace Controls

def allocation : Allocation := ⟨0, 7, 4096, 32, 16⟩
def view : View := ⟨⟨0, .read, 0, []⟩, 7, .u32, 1, 3, 4⟩

theorem counted_subrange : resolveHeld 8 1024 [allocation] view = some ⟨4100, 3, 4⟩ := by decide
theorem stale_same_address : resolveHeld 8 1024 [{allocation with incarnation := 8}] view = none := by decide
theorem uninitialized_tail : resolveHeld 8 1024 [allocation] {view with count := 4} = none := by decide
theorem count_overflow : resolveHeld 8 8 [allocation] view = none := by decide
theorem misaligned : resolveHeld 8 1024 [{allocation with base := 4097}] view = none := by decide
theorem overlapping_live_allocations : ¬ TableValid 65536
    [allocation, {allocation with root := 1, base := 4100}] := by decide
theorem unrepresentable_empty_address : resolveHeld 8 1024
    [{allocation with base := 2^64 - 16}] {view with offset := 4, count := 0} = none := by decide
theorem placement_positive : TableValid 65536
    [allocation, {allocation with root := 1, base := 8192}] := by decide

def source : CheckedBytes.Binding := ⟨0, .read, 0, []⟩
def destination : CheckedBytes.Binding := ⟨1, .write, 1, []⟩
def permissions : CheckedBytes.State := ⟨[source, destination], [0, 1], false, none⟩

theorem copy_permissions_valid : CheckedBytes.Valid permissions := by decide
theorem copy_permissions_usable :
    CheckedBytes.CanAccess permissions source false ∧
    CheckedBytes.CanAccess permissions destination true := by decide

def parent : CheckedBytes.Binding := ⟨0, .write, 0, []⟩
def child : CheckedBytes.Binding := ⟨1, .read, 0, [0]⟩
def reborrowed : CheckedBytes.State := ⟨[parent, child], [0], false, none⟩
theorem suspended_parent_refused : ¬ CheckedBytes.CanAccess reborrowed parent true := by decide
theorem child_usable : CheckedBytes.CanAccess reborrowed child false := by decide

theorem two_shared_aliases_allowed : CheckedBytes.CanAccess
    ⟨[source, ⟨1, .read, 0, []⟩], [0], false, none⟩ source false := by decide

end Controls
end Mettapedia.GSLT.LanguageDef.CheckedSpanPlacement
