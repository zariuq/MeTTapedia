import Mathlib.Data.BitVec
import Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation

/-!
# Certified finite-support compilation to bit vectors

An authored native type theory can expose a finite support inventory: rule
variables, binders, names subject to apartness, or another locally finite key
family.  This module compiles a source support list to a `BitVec` whose width
is exactly that inventory's size.

Admission is fail-closed: every source key must occur in the duplicate-free
inventory.  The refinement theorem identifies every decoded bit with source
membership.  Further theorems justify bitwise union and the standard
intersection-with-zero disjointness test.  No meaning of the keys is assumed.
-/

namespace Mettapedia.GSLT.LanguageDef.FiniteSupportBitVecCompilation

open FiniteEnvironmentCompilation

universe uKey

variable {Key : Type uKey} [DecidableEq Key]

/-- A packed support carrier whose width is fixed by the admitted inventory. -/
abbrev PackedSupport (inventory : Inventory Key) :=
  BitVec inventory.keys.length

/-- Compile source membership pointwise in inventory order. -/
def encode (inventory : Inventory Key) (support : List Key) :
    PackedSupport inventory :=
  let bits := inventory.keys.map fun key => support.contains key
  (BitVec.ofBoolListLE bits).cast
    (List.length_map (as := inventory.keys)
      (fun key => support.contains key))

/-- Read one source key through the generated inventory.  Undeclared query
keys observe `false`; undeclared source keys are separately rejected. -/
def decodeMember (inventory : Inventory Key)
    (packed : PackedSupport inventory) (key : Key) : Bool :=
  match inventory.resolve? key with
  | none => false
  | some slot => packed.getLsbD slot.val

/-- Executable recognizer for finite support. -/
def supported? (inventory : Inventory Key) (support : List Key) : Bool :=
  support.all fun key => (inventory.resolve? key).isSome

/-- Executable full-coverage test for a packed finite support.  The scan is
over the generated inventory, never over guest keys at runtime. -/
def packedFull? (inventory : Inventory Key)
    (packed : PackedSupport inventory) : Bool :=
  (List.range inventory.keys.length).all fun slot =>
    packed.getLsbD slot

/-- Support is accepted exactly when every key belongs to the inventory. -/
theorem supported?_eq_true_iff
    (inventory : Inventory Key) (support : List Key) :
    supported? inventory support = true ↔
      ∀ key ∈ support, key ∈ inventory.keys := by
  simp [supported?, Option.isSome_iff_exists,
    Inventory.exists_resolve?_eq_some_iff]

/-- Partial compiler for the admitted finite-support fragment. -/
def compile? (inventory : Inventory Key) (support : List Key) :
    Option (PackedSupport inventory) :=
  if supported? inventory support then some (encode inventory support)
  else none

/-- The compiler succeeds exactly when the local support recognizer accepts. -/
theorem compile?_isSome_eq_supported?
    (inventory : Inventory Key) (support : List Key) :
    (compile? inventory support).isSome = supported? inventory support := by
  unfold compile?
  cases supported? inventory support <;> rfl

/-- Each encoded slot is exactly membership of its reified source key. -/
theorem encode_getLsbD
    (inventory : Inventory Key) (support : List Key)
    (slot : inventory.Slot) :
    (encode inventory support).getLsbD slot.val =
      support.contains (inventory.reify slot) := by
  unfold encode
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  simp [Inventory.reify, List.getD, slot.isLt]

/-- A packed encoding covers every generated slot exactly when the source
support contains every key in the finite inventory. -/
theorem packedFull?_encode_eq_true_iff
    (inventory : Inventory Key) (support : List Key) :
    packedFull? inventory (encode inventory support) = true ↔
      ∀ key ∈ inventory.keys, key ∈ support := by
  constructor
  · intro full key keyMember
    obtain ⟨slot, selected⟩ :=
      (inventory.exists_resolve?_eq_some_iff key).2 keyMember
    have slotMember : slot.val ∈ List.range inventory.keys.length :=
      List.mem_range.mpr slot.isLt
    have bitSet := (List.all_eq_true.mp full) slot.val slotMember
    have reified :=
      (inventory.resolve?_eq_some_iff key slot).1 selected
    rw [encode_getLsbD, reified] at bitSet
    simpa [List.contains_eq_mem] using bitSet
  · intro covered
    rw [packedFull?, List.all_eq_true]
    intro slot slotMember
    have inRange : slot < inventory.keys.length :=
      List.mem_range.mp slotMember
    let finiteSlot : inventory.Slot := ⟨slot, inRange⟩
    change (encode inventory support).getLsbD finiteSlot.val = true
    rw [encode_getLsbD]
    have present : inventory.reify finiteSlot ∈ support :=
      covered (inventory.reify finiteSlot)
        (List.get_mem inventory.keys finiteSlot)
    simpa [List.contains_eq_mem] using present

/-- Complete membership refinement.  Once finite support is admitted, packed
lookup agrees with source-list membership for every key, including keys not in
the inventory. -/
theorem decodeMember_encode
    (inventory : Inventory Key) (support : List Key)
    (accepted : supported? inventory support = true) (key : Key) :
    decodeMember inventory (encode inventory support) key =
      support.contains key := by
  cases selected : inventory.resolve? key with
  | some slot =>
      simp only [decodeMember, selected]
      rw [encode_getLsbD]
      have reified :=
        (inventory.resolve?_eq_some_iff key slot).1 selected
      rw [reified]
  | none =>
      have absent : key ∉ support := by
        intro member
        have declared :=
          (supported?_eq_true_iff inventory support).1 accepted key member
        obtain ⟨slot, resolved⟩ :=
          (inventory.exists_resolve?_eq_some_iff key).2 declared
        rw [selected] at resolved
        contradiction
      simp [decodeMember, selected, List.contains_eq_mem, absent]

/-- Bitwise union implements union of supports represented by concatenation. -/
theorem encode_append
    (inventory : Inventory Key) (left right : List Key) :
    encode inventory (left ++ right) =
      encode inventory left ||| encode inventory right := by
  apply BitVec.eq_of_getLsbD_eq
  intro index inRange
  let slot : inventory.Slot := ⟨index, inRange⟩
  change (encode inventory (left ++ right)).getLsbD slot.val =
    (encode inventory left ||| encode inventory right).getLsbD slot.val
  rw [encode_getLsbD, BitVec.getLsbD_or,
    encode_getLsbD, encode_getLsbD]
  exact List.contains_append

/-- Source-level apartness/disjointness observation. -/
def SupportsDisjoint (left right : List Key) : Prop :=
  ∀ key, key ∈ left → key ∉ right

/-- The usual packed disjointness test is exact on admitted finite supports:
two supports are disjoint iff their bitwise intersection is zero. -/
theorem encode_and_eq_zero_iff
    (inventory : Inventory Key) (left right : List Key)
    (leftAccepted : supported? inventory left = true) :
    encode inventory left &&& encode inventory right = BitVec.zero _ ↔
      SupportsDisjoint left right := by
  constructor
  · intro intersectionZero key leftMember rightMember
    have declared :=
      (supported?_eq_true_iff inventory left).1
        leftAccepted key leftMember
    obtain ⟨slot, selected⟩ :=
      (inventory.exists_resolve?_eq_some_iff key).2 declared
    have reified :=
      (inventory.resolve?_eq_some_iff key slot).1 selected
    have observed := congrArg
      (fun bits : PackedSupport inventory => bits.getLsbD slot.val)
      intersectionZero
    rw [BitVec.getLsbD_and, encode_getLsbD, encode_getLsbD,
      reified] at observed
    simp [List.contains_eq_mem, leftMember, rightMember] at observed
  · intro disjoint
    apply BitVec.eq_of_getLsbD_eq
    intro index inRange
    let slot : inventory.Slot := ⟨index, inRange⟩
    change
      (encode inventory left &&& encode inventory right).getLsbD slot.val =
        (BitVec.zero inventory.keys.length).getLsbD slot.val
    rw [BitVec.getLsbD_and, encode_getLsbD, encode_getLsbD]
    by_cases leftMember : inventory.reify slot ∈ left
    · have rightAbsent := disjoint (inventory.reify slot) leftMember
      simp [List.contains_eq_mem, leftMember, rightAbsent]
    · simp [List.contains_eq_mem, leftMember]

/-- An admitted source support retains the exact compiler result. -/
structure AdmittedSupport (inventory : Inventory Key) where
  source : List Key
  compiled : PackedSupport inventory
  compile_eq : compile? inventory source = some compiled

/-- Run finite-support admission and retain its equation. -/
def admitSupport (inventory : Inventory Key) (source : List Key) :
    Option (AdmittedSupport inventory) :=
  match accepted : compile? inventory source with
  | none => none
  | some compiled => some { source, compiled, compile_eq := accepted }

/-- Bit-vector support lowering as a composable computed realization. -/
def bitVecSupportRealization (inventory : Inventory Key) :
    Mettapedia.GSLT.SimpleRealization
      (AdmittedSupport inventory)
      (PackedSupport inventory)
      (Key → Bool) where
  compile := fun _ admitted => admitted.compiled
  observeSource := fun _ admitted key => admitted.source.contains key
  observeArtifact := fun _ packed => decodeMember inventory packed
  adequate := by
    intro _ admitted
    funext key
    have recognized : supported? inventory admitted.source = true := by
      have compiledSome : (compile? inventory admitted.source).isSome = true := by
        rw [admitted.compile_eq]
        rfl
      rwa [compile?_isSome_eq_supported?] at compiledSome
    have compiledEq : admitted.compiled = encode inventory admitted.source := by
      have compileEq := admitted.compile_eq
      unfold compile? at compileEq
      rw [recognized] at compileEq
      exact Option.some.inj compileEq.symm
    rw [compiledEq]
    exact decodeMember_encode inventory admitted.source recognized key

/-! ## Cross-shape and rejection canaries -/

private inductive Field where
  | binder
  | body
  | support
  | apartness
deriving DecidableEq

private def fieldInventory : Inventory Field where
  keys := [.binder, .body, .support, .apartness]
  nodup := by decide

/-- A role-shaped support compiles to the expected four-bit carrier. -/
example :
    compile? fieldInventory [.binder, .apartness] =
      some (BitVec.ofNat 4 9) := by
  decide

/-- Numeric variable support uses the same compiler and membership theorem. -/
example :
    let inventory : Inventory Nat :=
      { keys := [10, 20, 30, 40, 50], nodup := by decide }
    decodeMember inventory (encode inventory [20, 50]) 50 = true := by
  decide

/-- Disjoint admitted supports have a zero packed intersection. -/
example :
    encode fieldInventory [.binder, .body] &&&
        encode fieldInventory [.support, .apartness] = BitVec.zero 4 := by
  decide

/-- A shared key remains visible to the packed intersection test. -/
example :
    encode fieldInventory [.binder, .body] &&&
        encode fieldInventory [.body, .support] ≠ BitVec.zero 4 := by
  decide

private inductive ExtendedField where
  | known
  | absent
deriving DecidableEq

private def restrictedInventory : Inventory ExtendedField where
  keys := [.known]
  nodup := by decide

/-- A genuinely absent key fails the negative admission gate. -/
example : (compile? restrictedInventory [.known, .absent]).isSome = false := by
  decide

end Mettapedia.GSLT.LanguageDef.FiniteSupportBitVecCompilation
