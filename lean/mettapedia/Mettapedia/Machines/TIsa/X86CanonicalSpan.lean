import Mettapedia.Machines.TIsa.X86DataStore

/-!
# Canonical spans and the shared native callback data contract

The unsigned predicate is the arithmetic projection of the HOL/s2n callback
contract: no unsigned wrap and a canonical address for every byte. Positive
spans project to the signed 48-bit geometry used by the original Sail body
proof. The stack additionally requires its post-return pointer canonical.

Physical-byte keys preserve equality and disjointness on this domain.
Counterexamples retain the distinction between signed ranges and unsigned
no-wrap spans, and show why canonical admission is necessary for the key map.

These are address and footprint laws. They do not import a HOL theorem or
establish agreement of complete ISA models. Mode, image placement, loaded
memory, call-site enforcement and ENDBR64 execution remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86CanonicalSpan

abbrev Word := BitVec 64

def Canonical (word : Word) : Prop :=
  word.toNat < 2 ^ 47 ∨ 2 ^ 64 - 2 ^ 47 ≤ word.toNat

instance (word : Word) : Decidable (Canonical word) :=
  inferInstanceAs (Decidable (word.toNat < 2 ^ 47 ∨ 2 ^ 64 - 2 ^ 47 ≤ word.toNat))

def Area (base : Word) (size : Nat) : Prop :=
  base.toNat + size ≤ 2 ^ 64 ∧
    ∀ offset < size, Canonical (base + BitVec.ofNat 64 offset)

def narrow (word : Word) : BitVec 48 := BitVec.ofInt 48 word.toInt

theorem canonical_iff_signed (word : Word) :
    Canonical word ↔ -(2 ^ 47 : Int) ≤ word.toInt ∧ word.toInt < 2 ^ 47 := by
  have bounded := BitVec.isLt word
  simp only [Canonical, BitVec.toInt_eq_toNat_cond]
  norm_num at bounded ⊢
  split_ifs <;> omega

theorem narrow_toInt (word : Word) (canonical : Canonical word) :
    (narrow word).toInt = word.toInt := by
  rcases (canonical_iff_signed word).mp canonical with ⟨lower, upper⟩
  exact BitVec.toInt_ofInt_eq_self (by decide) lower upper

theorem narrow_representation (word : Word) (canonical : Canonical word) :
    (narrow word).signExtend 64 = word := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide), narrow_toInt word canonical]

theorem add_toNat (word : Word) (offset : Nat)
    (within : word.toNat + offset < 2 ^ 64) :
    (word + BitVec.ofNat 64 offset).toNat = word.toNat + offset := by
  have small : offset < 2 ^ 64 := by omega
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
    Nat.mod_eq_of_lt within]

theorem area_base (word : Word) (size : Nat) (positive : 0 < size)
    (area : Area word size) : Canonical word := by
  simpa using area.2 0 positive

theorem area_signed_upper (word : Word) (size : Nat) (positive : 0 < size)
    (area : Area word size) : word.toInt + size ≤ (2 ^ 47 : Int) := by
  have base := area_base word size positive area
  rcases base with low | high
  · have bounded : word.toNat + size ≤ 2 ^ 47 := by
      by_contra exceeds
      have inside : 2 ^ 47 - word.toNat < size := by omega
      have sum : word.toNat + (2 ^ 47 - word.toNat) = 2 ^ 47 := by omega
      have byte := area.2 (2 ^ 47 - word.toNat) inside
      have address := add_toNat word (2 ^ 47 - word.toNat) (by rw [sum]; norm_num)
      simp only [Canonical, address, sum] at byte
      norm_num at byte
    have signed : word.toInt = (word.toNat : Int) := by
      rw [BitVec.toInt_eq_toNat_cond]
      norm_num at low
      split_ifs <;> omega
    rw [signed]
    exact_mod_cast bounded
  · have signed : word.toInt = (word.toNat : Int) - 2 ^ 64 := by
      rw [BitVec.toInt_eq_toNat_cond]
      norm_num at high ⊢
      omega
    rw [signed]
    have nowrap := area.1
    norm_num at nowrap ⊢
    omega

theorem low_toInt (word : Word) (low : word.toNat < 2 ^ 47) :
    word.toInt = (word.toNat : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]
  norm_num at low
  split_ifs <;> omega

theorem high_toInt (word : Word) (high : 2 ^ 64 - 2 ^ 47 ≤ word.toNat) :
    word.toInt = (word.toNat : Int) - 2 ^ 64 := by
  rw [BitVec.toInt_eq_toNat_cond]
  norm_num at high ⊢
  omega

theorem area_size (word : Word) (size : Nat) (positive : 0 < size)
    (area : Area word size) : size ≤ 2 ^ 47 := by
  rcases area_base word size positive area with low | high
  · have upper := area_signed_upper word size positive area
    rw [low_toInt word low] at upper
    omega
  · have nowrap := area.1
    norm_num at high nowrap ⊢
    omega

theorem area_signed_upper_strict (word : Word) (size : Nat) (positive : 0 < size)
    (area : Area word size) (after : Canonical (word + BitVec.ofNat 64 size)) :
    word.toInt + size < (2 ^ 47 : Int) := by
  have upper := area_signed_upper word size positive area
  by_contra failed
  have atLimit : word.toInt + size = (2 ^ 47 : Int) := by omega
  rcases area_base word size positive area with low | high
  · rw [low_toInt word low] at atLimit
    have sum : word.toNat + size = 2 ^ 47 := by exact_mod_cast atLimit
    have representation := add_toNat word size (by rw [sum]; norm_num)
    simp only [Canonical, representation, sum] at after
    norm_num at after
  · rw [high_toInt word high] at atLimit
    have nowrap := area.1
    norm_num at nowrap atLimit
    omega

theorem area_narrow_upper (word : Word) (size : Nat) (positive : 0 < size)
    (area : Area word size) : (narrow word).toInt + size ≤ (2 ^ 47 : Int) := by
  rw [narrow_toInt word (area_base word size positive area)]
  exact area_signed_upper word size positive area

theorem area_narrow_upper_strict (word : Word) (size : Nat) (positive : 0 < size)
    (area : Area word size) (after : Canonical (word + BitVec.ofNat 64 size)) :
    (narrow word).toInt + size < (2 ^ 47 : Int) := by
  rw [narrow_toInt word (area_base word size positive area)]
  exact area_signed_upper_strict word size positive area after

theorem offset_signed (word : Word) (size offset : Nat) (positive : 0 < size)
    (area : Area word size) (inside : offset < size) :
    (word + BitVec.ofNat 64 offset).toInt = word.toInt + offset := by
  have small : offset < 2 ^ 47 := lt_of_lt_of_le inside (area_size word size positive area)
  have offsetSigned : (BitVec.ofNat 64 offset).toInt = (offset : Int) := by
    rw [BitVec.toInt_ofNat']
    apply Int.bmod_eq_of_le
    · norm_num
    · norm_num at small ⊢; omega
  rw [BitVec.toInt_add, offsetSigned]
  apply Int.bmod_eq_of_le
  · have lower := ((canonical_iff_signed word).mp (area_base word size positive area)).1
    norm_num at lower ⊢
    omega
  · have upper := area_signed_upper word size positive area
    norm_num at upper ⊢
    omega

theorem offset_representation (word : Word) (size offset : Nat) (positive : 0 < size)
    (area : Area word size) (inside : offset < size) :
    (Mettapedia.Machines.TIsa.X86Execution.address (narrow word).toInt offset).signExtend 64 =
      word + BitVec.ofNat 64 offset := by
  have base := area_base word size positive area
  have lower := ((canonical_iff_signed word).mp base).1
  have upper := area_signed_upper word size positive area
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide)]
  unfold Mettapedia.Machines.TIsa.X86Execution.address
  rw [BitVec.toInt_ofInt_eq_self (by decide) (by rw [narrow_toInt word base]; omega)
      (by rw [narrow_toInt word base]; omega), narrow_toInt word base,
      offset_signed word size offset positive area inside]

theorem successor_representation (word : Word) (size : Nat) (positive : 0 < size)
    (area : Area word size) (canonicalAfter : Canonical (word + BitVec.ofNat 64 size)) :
    (Mettapedia.Machines.TIsa.X86Execution.address (narrow word).toInt size).signExtend 64 =
      word + BitVec.ofNat 64 size := by
  have base := area_base word size positive area
  have small := area_size word size positive area
  have lower := ((canonical_iff_signed word).mp base).1
  have upper := area_signed_upper_strict word size positive area canonicalAfter
  have sizeSigned : (BitVec.ofNat 64 size).toInt = (size : Int) := by
    rw [BitVec.toInt_ofNat']
    apply Int.bmod_eq_of_le
    · norm_num
    · norm_num at small ⊢
      omega
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide)]
  unfold Mettapedia.Machines.TIsa.X86Execution.address
  rw [BitVec.toInt_ofInt_eq_self (by decide) (by rw [narrow_toInt word base]; omega)
      (by rw [narrow_toInt word base]; omega), narrow_toInt word base, BitVec.toInt_add, sizeSigned]
  symm
  apply Int.bmod_eq_of_le
  · norm_num at lower ⊢
    omega
  · norm_num at upper ⊢
    omega

def physicalKey (word : Word) : Nat := ((narrow word).signExtend 52).toNat

theorem physicalKey_injective (left right : Word)
    (leftCanonical : Canonical left) (rightCanonical : Canonical right)
    (same : physicalKey left = physicalKey right) : left = right := by
  have words : (narrow left).signExtend 52 = (narrow right).signExtend 52 :=
    BitVec.eq_of_toNat_eq same
  apply BitVec.eq_of_toInt_eq
  have signed := congrArg BitVec.toInt words
  simpa only [BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 52),
    narrow_toInt left leftCanonical, narrow_toInt right rightCanonical] using signed

theorem narrow_mod8 (word : Word) (canonical : Canonical word) :
    (narrow word).toNat % 8 = word.toNat % 8 := by
  conv_rhs => rw [← narrow_representation word canonical]
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth_of_le (by decide)]
  split_ifs <;> simp [Nat.add_mod]

theorem narrow_aligned (word : Word) (canonical : Canonical word)
    (aligned : word.toNat % 8 = 0) : (narrow word) &&& (7#48) = (0#48) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (7#48).toNat = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  simpa using (narrow_mod8 word canonical).trans aligned

theorem narrow_offset (word : Word) (size offset : Nat) (positive : 0 < size)
    (area : Area word size) (inside : offset < size) :
    narrow (word + BitVec.ofNat 64 offset) =
      Mettapedia.Machines.TIsa.X86Execution.address (narrow word).toInt offset := by
  apply BitVec.eq_of_toInt_eq
  have equality := congrArg BitVec.toInt (offset_representation word size offset positive area inside)
  rw [BitVec.toInt_signExtend_of_le (by decide)] at equality
  rw [narrow_toInt _ (area.2 offset inside)]
  exact equality.symm

theorem physicalKey_offset (word : Word) (size offset : Nat) (positive : 0 < size)
    (area : Area word size) (inside : offset < size) :
    physicalKey (word + BitVec.ofNat 64 offset) =
      Mettapedia.Machines.TIsa.X86WriteWords.physicalAddress (narrow word) offset := by
  simp only [physicalKey, narrow_offset word size offset positive area inside,
    Mettapedia.Machines.TIsa.X86WriteWords.physicalAddress]

theorem physicalAddress_nested (word : Word) (size first second : Nat) (positive : 0 < size)
    (area : Area word size) (inside : first + second < size) :
    Mettapedia.Machines.TIsa.X86WriteWords.physicalAddress
      (Mettapedia.Machines.TIsa.X86Execution.address (narrow word).toInt first) second =
      physicalKey (word + BitVec.ofNat 64 (first + second)) := by
  have firstInside : first < size := by omega
  have coordinate : (Mettapedia.Machines.TIsa.X86Execution.address (narrow word).toInt first).toInt =
      (narrow word).toInt + first := by
    rw [← narrow_offset word size first positive area firstInside,
      narrow_toInt _ (area.2 first firstInside), offset_signed word size first positive area firstInside,
      narrow_toInt _ (area_base word size positive area)]
  rw [physicalKey_offset word size (first + second) positive area inside]
  simp only [Mettapedia.Machines.TIsa.X86WriteWords.physicalAddress]
  rw [coordinate]
  simp only [Mettapedia.Machines.TIsa.X86Execution.address, Nat.cast_add, Int.add_assoc]

theorem outside_output (output other : Word) (outputArea : Area output 8)
    (otherCanonical : Canonical other)
    (apart : ∀ byte < 8, output + BitVec.ofNat 64 byte ≠ other) :
    physicalKey other ∉ Mettapedia.Machines.TIsa.X86DataStore.writes true (narrow output) := by
  intro member
  obtain ⟨offset, present, same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  have inside : offset < 8 := List.mem_range.mp present
  have coordinate := physicalKey_offset output 8 offset (by decide) outputArea inside
  apply apart offset inside
  apply physicalKey_injective _ _ (outputArea.2 offset inside) otherCanonical
  exact coordinate.trans same

theorem separated_of_order (left right : Word) (leftSize rightSize : Nat)
    (leftArea : Area left leftSize) (rightArea : Area right rightSize)
    (ordered : left.toNat + leftSize ≤ right.toNat) :
    ∀ i < leftSize, ∀ j < rightSize,
      left + BitVec.ofNat 64 i ≠ right + BitVec.ofNat 64 j := by
  intro i hi j hj same
  have values := congrArg BitVec.toNat same
  rw [add_toNat left i (by have := leftArea.1; omega),
    add_toNat right j (by have := rightArea.1; omega)] at values
  omega

theorem offset_aligned (word : Word) (size offset : Nat) (positive : 0 < size)
    (area : Area word size) (inside : offset < size)
    (aligned : word.toNat % 8 = 0) (alignedOffset : offset % 8 = 0) :
    Mettapedia.Machines.TIsa.X86Execution.address (narrow word).toInt offset &&& (7#48) = (0#48) := by
  rw [← narrow_offset word size offset positive area inside]
  apply narrow_aligned _ (area.2 offset inside)
  rw [add_toNat word offset (by have := area.1; omega)]
  simp [Nat.add_mod, aligned, alignedOffset]

theorem area_low (word : Word) (size : Nat) (upper : word.toNat + size ≤ 2 ^ 47) :
    Area word size := by
  constructor
  · norm_num at upper ⊢
    omega
  · intro offset inside
    apply Or.inl
    rw [add_toNat word offset (by norm_num at upper ⊢; omega)]
    omega

theorem area_high (word : Word) (size : Nat)
    (high : 2 ^ 64 - 2 ^ 47 ≤ word.toNat) (nowrap : word.toNat + size ≤ 2 ^ 64) :
    Area word size := by
  refine ⟨nowrap, ?_⟩
  intro offset inside
  apply Or.inr
  rw [add_toNat word offset (by omega)]
  omega

structure SharedDataEntry where
  input : Word
  output : Word
  stack : Word
  target : Word
  inputArea : Area input 16
  outputArea : Area output 8
  stackArea : Area stack 8
  inputAligned : input.toNat % 8 = 0
  outputAligned : output.toNat % 8 = 0
  stackAligned : stack.toNat % 8 = 0
  targetCanonical : Canonical target
  nextStackCanonical : Canonical (stack + (8#64))

structure DataGeometry (entry : SharedDataEntry) where
  buffer : BitVec 48
  output : BitVec 48
  stack : BitVec 48
  target : BitVec 48
  inputRep : buffer.signExtend 64 = entry.input
  outputRep : output.signExtend 64 = entry.output
  stackRep : stack.signExtend 64 = entry.stack
  targetRep : target.signExtend 64 = entry.target
  inputUpper : buffer.toInt + 16 ≤ (2 ^ 47 : Int)
  outputUpper : output.toInt + 8 ≤ (2 ^ 47 : Int)
  stackUpper : stack.toInt + 8 < (2 ^ 47 : Int)
  inputAligned : ∀ slot : Fin 2,
    Mettapedia.Machines.TIsa.X86Execution.address buffer.toInt (8 * slot.val) &&& (7#48) = (0#48)
  outputAligned : output &&& (7#48) = (0#48)
  stackAligned : stack &&& (7#48) = (0#48)

def SharedDataEntry.geometry (entry : SharedDataEntry) : DataGeometry entry where
  buffer := narrow entry.input
  output := narrow entry.output
  stack := narrow entry.stack
  target := narrow entry.target
  inputRep := narrow_representation _ (area_base _ _ (by decide) entry.inputArea)
  outputRep := narrow_representation _ (area_base _ _ (by decide) entry.outputArea)
  stackRep := narrow_representation _ (area_base _ _ (by decide) entry.stackArea)
  targetRep := narrow_representation _ entry.targetCanonical
  inputUpper := area_narrow_upper _ _ (by decide) entry.inputArea
  outputUpper := area_narrow_upper _ _ (by decide) entry.outputArea
  stackUpper := area_narrow_upper_strict _ _ (by decide) entry.stackArea entry.nextStackCanonical
  inputAligned slot := offset_aligned _ 16 (8 * slot.val) (by decide) entry.inputArea
    (by have := slot.isLt; omega) entry.inputAligned (by omega)
  outputAligned := narrow_aligned _ (area_base _ _ (by decide) entry.outputArea) entry.outputAligned
  stackAligned := narrow_aligned _ (area_base _ _ (by decide) entry.stackArea) entry.stackAligned

theorem physical_images_disjoint (left right : Set Word)
    (leftCanonical : ∀ word ∈ left, Canonical word)
    (rightCanonical : ∀ word ∈ right, Canonical word) :
    Disjoint (physicalKey '' left) (physicalKey '' right) ↔ Disjoint left right := by
  constructor
  · intro apart
    rw [Set.disjoint_left] at apart ⊢
    intro word inLeft inRight
    exact apart ⟨word, inLeft, rfl⟩ ⟨word, inRight, rfl⟩
  · intro apart
    rw [Set.disjoint_left] at apart ⊢
    intro key inLeft inRight
    obtain ⟨a, ha, pa⟩ := inLeft
    obtain ⟨b, hb, pb⟩ := inRight
    have same := physicalKey_injective a b (leftCanonical a ha) (rightCanonical b hb) (pa.trans pb.symm)
    subst b
    exact apart ha hb

namespace Controls

def lowEntry : SharedDataEntry where
  input := 4096#64
  output := 8192#64
  stack := 12288#64
  target := 16384#64
  inputArea := area_low _ _ (by decide)
  outputArea := area_low _ _ (by decide)
  stackArea := area_low _ _ (by decide)
  inputAligned := by decide
  outputAligned := by decide
  stackAligned := by decide
  targetCanonical := by decide
  nextStackCanonical := by decide

theorem low_geometry :
    lowEntry.geometry.buffer = (4096#48) ∧ lowEntry.geometry.output = (8192#48) ∧
      lowEntry.geometry.stack = (12288#48) ∧ lowEntry.geometry.target = (16384#48) := by decide

def highStackEntry : SharedDataEntry :=
  { lowEntry with
    stack := (-8#64)
    stackArea := area_high _ _ (by decide) (by decide)
    stackAligned := by decide
    nextStackCanonical := by decide }

theorem high_stack_returns_to_zero :
    (highStackEntry.stack + (8#64)) = (0#64) ∧
      highStackEntry.geometry.stack.toInt + 8 = 0 := by decide

theorem signed_zero_crossing :
    (narrow (-8#64)).toInt + 16 ≤ (2 ^ 47 : Int) := by decide

theorem unsigned_zero_crossing_refused : ¬ Area (-8#64) 16 := by
  intro area
  have nowrap := area.1
  norm_num at nowrap

theorem low_end_inclusive :
    Area (140737488355312#64) 16 ∧
      (narrow (140737488355312#64)).toInt + 16 = (2 ^ 47 : Int) := by
  exact ⟨area_low _ _ (by decide), by decide⟩

theorem stack_end_requires_post_canonical :
    Area (140737488355320#64) 8 ∧
      ¬ Canonical ((140737488355320#64) + (8#64)) ∧
      ¬ (narrow (140737488355320#64)).toInt + 8 < (2 ^ 47 : Int) := by
  exact ⟨area_low _ _ (by decide), by decide, by decide⟩

theorem canonical_keys_distinct : physicalKey (-1#64) ≠ physicalKey (0#64) := by decide

theorem unrestricted_key_alias :
    physicalKey (281474976710656#64) = physicalKey (0#64) ∧
      ¬ Canonical (281474976710656#64) := by decide

theorem empty_area_does_not_admit_base :
    Area (140737488355328#64) 0 ∧ ¬ Canonical (140737488355328#64) := by
  constructor
  · constructor
    · decide
    · intro offset within
      omega
  · decide

end Controls

#print axioms canonical_iff_signed
#print axioms narrow_representation
#print axioms area_signed_upper
#print axioms area_narrow_upper_strict
#print axioms offset_representation
#print axioms physicalKey_injective
#print axioms successor_representation
#print axioms outside_output
#print axioms SharedDataEntry.geometry
#print axioms physical_images_disjoint
#print axioms Controls.signed_zero_crossing
#print axioms Controls.unsigned_zero_crossing_refused
#print axioms Controls.stack_end_requires_post_canonical

end Mettapedia.Machines.TIsa.X86CanonicalSpan
