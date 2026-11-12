import Mettapedia.Machines.TIsa.P1Scalar
import Mettapedia.Machines.TIsa.Memory

/-!
# p1 byte-memory and address instructions as transform recipes

The source vocabulary selects the existing capability, register and physical
byte cells. ADDR checks its indexed intermediate pointer and displaced result
separately. Loads normalize at the declared value width, not the memory width;
BOOL values are checked rather than masked. Stores reuse the byte-resource
store law and retain its exact footprint.

Bounds failures read no out-of-range byte. A noncanonical BOOL load has its
own readonly failure recipe. These failures transfer control to the supplied
invalid-input handler; the handler's frame writes have a separate contract.
Frame loads use the internal read-only frame view (region 255); its base,
length 192 and byte backing are entry-encoding obligations.

The integer inside-test correspondence requires a nonwrapping capability and
an in-region pointer. Establishing this typing invariant from actual admission
and preserving it through a whole program remain separate obligations, as do
whole-program hosting and native refinement.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.P1Memory

open P1Source Cells CellEffects

abbrev Key := Memory.Key Reg

def address? (range : ByteRange) (pointer index scale : Nat) (displacement : Int) : Option Nat := do
  let intermediate ← checkedAddress? range pointer index scale 0
  checkedAddress? range intermediate 0 0 displacement

theorem address?_iff (range : ByteRange) (pointer index scale address : Nat) (displacement : Int) :
    address? range pointer index scale displacement = some address ↔
      ∃ intermediate,
        checkedAddress? range pointer index scale 0 = some intermediate ∧
        checkedAddress? range intermediate 0 0 displacement = some address := by
  simp [address?, Option.bind_eq_some_iff]

theorem address?_inside (range : ByteRange) (pointer index scale address : Nat) (displacement : Int)
    (formed : address? range pointer index scale displacement = some address) :
    range.base ≤ address ∧ address ≤ range.stop := by
  obtain ⟨intermediate, _, second⟩ := (address?_iff range pointer index scale address displacement).mp formed
  exact checkedAddress_in_capability range intermediate 0 0 address displacement second

theorem address?_no_wrap (range : ByteRange) (pointer index scale address : Nat) (displacement : Int)
    (formed : address? range pointer index scale displacement = some address) :
    address < 2 ^ 64 := by
  obtain ⟨intermediate, _, second⟩ := (address?_iff range pointer index scale address displacement).mp formed
  exact (checkedAddress_no_wrap range intermediate 0 0 address displacement second).2.2

def checkedWord (ty : TypeTag) (value : Word) : Option Word :=
  if P1Scalar.boolInputs ty [value] then some (P1Scalar.normalize ty value) else none

theorem checkedWord_none_iff (ty : TypeTag) (value : Word) :
    checkedWord ty value = none ↔ ty = .boolean ∧ 1 < value.toNat := by
  cases ty <;> simp [checkedWord, P1Scalar.boolInputs]

def loadValue (ty : TypeTag) (bytes : List Word) : Option Word :=
  (Memory.readByteWords? bytes).bind fun bytes => checkedWord ty (packBytes bytes)

theorem read_byteWords (bytes : List (BitVec 8)) :
    Memory.readByteWords? (Memory.byteWords bytes) = some bytes := by
  have bound : ∀ byte : BitVec 8, (byte.zeroExtend 64).toNat < 256 := by
    intro byte
    simpa only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
      (lt_of_lt_of_le byte.isLt (by decide : 2 ^ 8 ≤ 2 ^ 64))] using byte.isLt
  have extracts : ∀ byte : BitVec 8, (byte.zeroExtend 64).extractLsb' 0 8 = byte := by
    intro byte
    apply BitVec.eq_of_getLsbD_eq
    intro bit within
    have wide : bit < 64 := by omega
    simp [within, wide]
  have all : (Memory.byteWords bytes).all (fun value => decide (value.toNat < 256)) = true := by
    apply List.all_eq_true.mpr
    intro value member
    obtain ⟨byte, _, rfl⟩ := List.mem_map.mp member
    exact decide_eq_true (bound byte)
  simp only [Memory.readByteWords?, all, if_true]
  simp [Memory.byteWords, List.map_map, Function.comp_def, extracts]

theorem load_byteWords (ty : TypeTag) (bytes : List (BitVec 8)) :
    loadValue ty (Memory.byteWords bytes) = checkedWord ty (packBytes bytes) := by
  rw [loadValue, read_byteWords]
  rfl

theorem access?_iff_inside (base length pointer : Word) (displacement : BitVec 32)
    (width address : Nat)
    (rangeFits : base.toNat + length.toNat < 2 ^ 64)
    (pointerLower : base.toNat ≤ pointer.toNat)
    (pointerUpper : pointer.toNat ≤ base.toNat + length.toNat) :
    Memory.access? base length pointer displacement.toInt width = some address ↔
      (base.toNat : Int) ≤ (pointer.toNat : Int) + displacement.toInt ∧
      (pointer.toNat : Int) + displacement.toInt + width ≤ (base.toNat : Int) + length.toNat ∧
      address = ((pointer.toNat : Int) + displacement.toInt).toNat := by
  let range : ByteRange := ⟨base.toNat, length.toNat⟩
  have valid : range.valid64 = true := by
    change decide (base.toNat < 2 ^ 64 ∧ base.toNat + length.toNat ≤ 2 ^ 64) = true
    exact decide_eq_true ⟨base.isLt, by omega⟩
  have lowerDisp : -(2 ^ 31 : Int) ≤ displacement.toInt := by
    simpa using displacement.le_toInt
  have upperDisp : displacement.toInt < (2 ^ 31 : Int) := by
    simpa using displacement.toInt_lt
  have pointerBound := pointer.isLt
  constructor
  · intro read
    simp only [Memory.access?, Option.bind_eq_bind, Option.bind_eq_some_iff] at read
    obtain ⟨formed, first, second⟩ := read
    obtain ⟨admitted, formedValue⟩ :=
      (checkedAddress?_iff range pointer.toNat 0 0 formed displacement.toInt).mp first
    rcases admitted with ⟨_, _, _, _, _, _, _, _, nonnegative, _, lower, upper⟩
    obtain ⟨_, _, within, result⟩ := (range.access?_iff (formed - range.base) width address).mp second
    simp only [addressTarget, addressSum, Nat.zero_mul, Nat.add_zero] at formedValue nonnegative lower upper
    dsimp [range, ByteRange.stop] at within result lower upper
    have formedInt : (formed : Int) = (pointer.toNat : Int) + displacement.toInt := by omega
    have same : address = formed := by omega
    exact ⟨lower, by omega, by omega⟩
  · rintro ⟨lower, upper, rfl⟩
    let formed := ((pointer.toNat : Int) + displacement.toInt).toNat
    have nonnegative : 0 ≤ (pointer.toNat : Int) + displacement.toInt := by omega
    have formedInt : (formed : Int) = (pointer.toNat : Int) + displacement.toInt := by
      dsimp [formed]
      omega
    have admitted : AddressAdmitted range pointer.toNat 0 0 displacement.toInt := by
      simp only [AddressAdmitted, valid, true_and, addressTarget, addressSum,
        Nat.zero_mul, Nat.add_zero]
      dsimp [range, ByteRange.stop]
      omega
    have first : checkedAddress? range pointer.toNat 0 0 displacement.toInt = some formed :=
      (checkedAddress?_iff range pointer.toNat 0 0 formed displacement.toInt).mpr
        ⟨admitted, by simp [formed, addressTarget, addressSum]⟩
    unfold Memory.access?
    change (checkedAddress? range pointer.toNat 0 0 displacement.toInt >>= fun address =>
      range.access? (address - range.base) width) = some formed
    rw [first]
    change range.access? (formed - range.base) width = some formed
    apply (range.access?_iff (formed - range.base) width formed).mpr
    dsimp [range, ByteRange.stop]
    exact ⟨base.isLt, by omega, by omega, by omega⟩

def loadRecipe (ty : TypeTag) (width : P1Source.Width) (region : Nat) (destination pointer : Reg)
    (displacement : Int) (address : Nat) : Recipe Key where
  inputs := Memory.capabilityKeys region ++ .register pointer :: Memory.byteKeys address width.bytes
  outputs := [.register destination]
  guard := fun inputs outputs => match inputs, outputs with
    | base :: length :: mode :: pointer :: bytes, [result] =>
        (mode == 1 || mode == 2) &&
        Memory.access? base length pointer displacement width.bytes == some address &&
        bytes.length == width.bytes && loadValue ty bytes == some result
    | _, _ => false

theorem load_guard_iff (ty : TypeTag) (width : P1Source.Width) (region : Nat) (destination pointer : Reg)
    (displacement : Int) (address : Nat) (before after : Key → Word) :
    (loadRecipe ty width region destination pointer displacement address).guard
      ((loadRecipe ty width region destination pointer displacement address).inputs.map before)
      ((loadRecipe ty width region destination pointer displacement address).outputs.map after) = true ↔
      (before (.capabilityMode region) = 1 ∨ before (.capabilityMode region) = 2) ∧
      Memory.access? (before (.capabilityBase region)) (before (.capabilityLength region))
        (before (.register pointer)) displacement width.bytes = some address ∧
      loadValue ty ((Memory.byteKeys address width.bytes).map before) = some (after (.register destination)) := by
  simp [loadRecipe, Memory.capabilityKeys, Memory.byteKeys, Bool.and_eq_true, and_assoc]

theorem load_overwrite_eq (ty : TypeTag) (width : P1Source.Width) (region : Nat) (destination pointer : Reg)
    (displacement : Int) (address : Nat) (before after : Key → Word) :
    overwrite (loadRecipe ty width region destination pointer displacement address).writes before after =
      Function.update before (.register destination) (after (.register destination)) := by
  funext key
  by_cases same : key = .register destination
  · subst key; simp [overwrite, Recipe.writes, loadRecipe]
  · simp [overwrite, Recipe.writes, loadRecipe, same]

theorem load_rewrite_iff (ty : TypeTag) (width : P1Source.Width) (region : Nat) (destination pointer : Reg)
    (displacement : Int) (address : Nat) (keys : Finset Key) (before : Key → Word)
    (world : Multiset (Cell Key)) :
    (profile [loadRecipe ty width region destination pointer displacement address]).theory.rewrites
      (encode keys before) world ↔
      ∃ result, (loadRecipe ty width region destination pointer displacement address).support ⊆ keys ∧
        (before (.capabilityMode region) = 1 ∨ before (.capabilityMode region) = 2) ∧
        Memory.access? (before (.capabilityBase region)) (before (.capabilityLength region))
          (before (.register pointer)) displacement width.bytes = some address ∧
        loadValue ty ((Memory.byteKeys address width.bytes).map before) = some result ∧
        world = encode keys (Function.update before (.register destination) result) := by
  rw [profile_rewrite_iff]
  constructor
  · rintro ⟨effect, member, after, included, guarded, endpoint⟩
    have same : effect = loadRecipe ty width region destination pointer displacement address := by simpa using member
    subst effect
    obtain ⟨mode, access, value⟩ := (load_guard_iff ty width region destination pointer displacement address before after).mp guarded
    exact ⟨after (.register destination), included, mode, access, value,
      by rw [endpoint, load_overwrite_eq]⟩
  · rintro ⟨result, included, mode, access, value, endpoint⟩
    refine ⟨loadRecipe ty width region destination pointer displacement address, by simp,
      Function.update before (.register destination) result, included, ?_, ?_⟩
    · apply (load_guard_iff ty width region destination pointer displacement address before _).mpr
      exact ⟨mode, access, by simpa using value⟩
    · simpa only [load_overwrite_eq, Function.update_self] using endpoint

def memoryWidth : P1Source.Width → Memory.Width
  | .byte => .byte | .word32 => .word32 | .word64 => .word64

theorem memoryWidth_bytes (width : P1Source.Width) : (memoryWidth width).bytes = width.bytes := by
  cases width <;> rfl

def storeSpec (width : P1Source.Width) (region : Nat) (pointer source : Reg)
    (displacement : Int) : Memory.Store Reg :=
  ⟨⟨region, pointer, displacement, memoryWidth width⟩, source⟩

def storeRecipe (width : P1Source.Width) (region : Nat) (pointer source : Reg)
    (displacement : Int) (address : Nat) : Recipe Key :=
  (storeSpec width region pointer source displacement).recipe address

theorem store_guard_iff (width : P1Source.Width) (region : Nat) (pointer source : Reg)
    (displacement : Int) (address : Nat) (before after : Key → Word) :
    (storeRecipe width region pointer source displacement address).guard
      ((storeRecipe width region pointer source displacement address).inputs.map before)
      ((storeRecipe width region pointer source displacement address).outputs.map after) = true ↔
      before (.capabilityMode region) = 2 ∧
      Memory.access? (before (.capabilityBase region)) (before (.capabilityLength region))
        (before (.register pointer)) displacement width.bytes = some address ∧
      (Memory.byteKeys address width.bytes).map after =
        Memory.byteWords (unpackBytes width.bytes (before (.register source))) := by
  simpa only [storeRecipe, storeSpec, memoryWidth_bytes] using
    (storeSpec width region pointer source displacement).guard_iff address before after

theorem store_preserves_outside (width : P1Source.Width) (region : Nat) (pointer source : Reg)
    (displacement : Int) (address other : Nat) (before after : Key → Word)
    (outside : other < address ∨ address + width.bytes ≤ other) :
    overwrite (storeRecipe width region pointer source displacement address).writes before after (.byte other) =
      before (.byte other) := by
  exact (storeSpec width region pointer source displacement).preserves_outside address other before after
    (by simpa only [storeSpec, memoryWidth_bytes] using outside)

def indexValue? : Option Reg → List Word → Option Word
  | none, [] => some 0
  | some _, [value] => some value
  | _, _ => none

def addressValue (base length pointer : Word) (scale : Fin 4) (displacement : BitVec 32)
    (index : Word) : Option Word :=
  (address? ⟨base.toNat, length.toNat⟩ pointer.toNat index.toNat scale.val displacement.toInt).map (BitVec.ofNat 64)

def addressRecipe (region : Nat) (destination pointer : Reg) (index : Option Reg)
    (scale : Fin 4) (displacement : BitVec 32) : Recipe Key where
  inputs := Memory.capabilityKeys region ++ [.register pointer] ++ (index.toList.map Memory.Key.register)
  outputs := [.register destination]
  guard := fun inputs outputs => match inputs, outputs with
    | base :: length :: mode :: pointer :: values, [result] =>
        (mode == 1 || mode == 2) &&
        ((indexValue? index values).bind (addressValue base length pointer scale displacement)) == some result
    | _, _ => false

theorem address_guard_iff (region : Nat) (destination pointer : Reg) (index : Option Reg)
    (scale : Fin 4) (displacement : BitVec 32) (before after : Key → Word) :
    (addressRecipe region destination pointer index scale displacement).guard
      ((addressRecipe region destination pointer index scale displacement).inputs.map before)
      ((addressRecipe region destination pointer index scale displacement).outputs.map after) = true ↔
      (before (.capabilityMode region) = 1 ∨ before (.capabilityMode region) = 2) ∧
      addressValue (before (.capabilityBase region)) (before (.capabilityLength region))
        (before (.register pointer)) scale displacement
        (match index with | none => 0 | some index => before (.register index)) =
          some (after (.register destination)) := by
  cases index <;> simp [addressRecipe, Memory.capabilityKeys, indexValue?, Bool.and_eq_true]

theorem addressValue_inside (base length pointer index result : Word) (scale : Fin 4)
    (displacement : BitVec 32)
    (computed : addressValue base length pointer scale displacement index = some result) :
    base.toNat ≤ result.toNat ∧ result.toNat ≤ base.toNat + length.toNat := by
  unfold addressValue at computed
  obtain ⟨address, formed, rfl⟩ := Option.map_eq_some_iff.mp computed
  have noWrap := address?_no_wrap _ _ _ _ _ _ formed
  have inside := address?_inside _ _ _ _ _ _ formed
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt noWrap, ByteRange.stop] using inside

def memoryRecipe? (instruction : Instr) (address : Nat) : Option (Recipe Key) :=
  match instruction with
  | .load ty width region destination pointer displacement =>
      some (loadRecipe ty width region.val destination pointer displacement.toInt address)
  | .loadFrame ty destination slot =>
      some (loadRecipe ty .word64 255 destination 0 (8 * slot.val) address)
  | .store width region pointer displacement source =>
      some (storeRecipe width region.val pointer source displacement.toInt address)
  | .address region destination pointer index scale displacement =>
      some (addressRecipe region.val destination pointer index scale displacement)
  | _ => none

def boundsFailureRecipe (write : Bool) (width : P1Source.Width) (region : Nat) (pointer : Reg)
    (displacement : Int) : Recipe Key where
  inputs := Memory.capabilityKeys region ++ [.register pointer]
  outputs := []
  guard := fun inputs outputs => match inputs with
    | [base, length, mode, pointer] => outputs.isEmpty &&
        (if write then mode == 2 else mode == 1 || mode == 2) &&
        (Memory.access? base length pointer displacement width.bytes).isNone
    | _ => false

theorem bounds_failure_guard_iff (write : Bool) (width : P1Source.Width) (region : Nat) (pointer : Reg)
    (displacement : Int) (before after : Key → Word) :
    (boundsFailureRecipe write width region pointer displacement).guard
      ((boundsFailureRecipe write width region pointer displacement).inputs.map before)
      ((boundsFailureRecipe write width region pointer displacement).outputs.map after) = true ↔
      (if write then before (.capabilityMode region) = 2
       else before (.capabilityMode region) = 1 ∨ before (.capabilityMode region) = 2) ∧
      Memory.access? (before (.capabilityBase region)) (before (.capabilityLength region))
        (before (.register pointer)) displacement width.bytes = none := by
  cases write <;> simp [boundsFailureRecipe, Memory.capabilityKeys, Bool.and_eq_true]

def loadBooleanFailureRecipe (ty : TypeTag) (width : P1Source.Width) (region : Nat) (pointer : Reg)
    (displacement : Int) (address : Nat) : Recipe Key where
  inputs := Memory.capabilityKeys region ++ .register pointer :: Memory.byteKeys address width.bytes
  outputs := []
  guard := fun inputs outputs => match inputs with
    | base :: length :: mode :: pointer :: bytes => outputs.isEmpty && ty == .boolean &&
        (mode == 1 || mode == 2) &&
        Memory.access? base length pointer displacement width.bytes == some address &&
        bytes.length == width.bytes &&
        ((Memory.readByteWords? bytes).map packBytes).any (fun word => decide (1 < word.toNat))
    | _ => false

theorem load_boolean_failure_guard_iff (ty : TypeTag) (width : P1Source.Width) (region : Nat) (pointer : Reg)
    (displacement : Int) (address : Nat) (before after : Key → Word) :
    (loadBooleanFailureRecipe ty width region pointer displacement address).guard
      ((loadBooleanFailureRecipe ty width region pointer displacement address).inputs.map before)
      ((loadBooleanFailureRecipe ty width region pointer displacement address).outputs.map after) = true ↔
      ty = .boolean ∧
      (before (.capabilityMode region) = 1 ∨ before (.capabilityMode region) = 2) ∧
      Memory.access? (before (.capabilityBase region)) (before (.capabilityLength region))
        (before (.register pointer)) displacement width.bytes = some address ∧
      ∃ bytes, Memory.readByteWords? ((Memory.byteKeys address width.bytes).map before) = some bytes ∧
        1 < (packBytes bytes).toNat := by
  have any_iff (decoded : Option (List (BitVec 8))) :
      (decoded.map packBytes).any (fun word => decide (1 < word.toNat)) = true ↔
        ∃ bytes, decoded = some bytes ∧ 1 < (packBytes bytes).toNat := by
    cases decoded <;> simp
  simp [loadBooleanFailureRecipe, Memory.capabilityKeys, Memory.byteKeys, Bool.and_eq_true, and_assoc, any_iff]

theorem load_cases_complete (ty : TypeTag) (width : P1Source.Width) (region : Nat)
    (destination pointer : Reg) (displacement : Int) (address : Nat) (before : Key → Word)
    (bytes : List (BitVec 8))
    (mode : before (.capabilityMode region) = 1 ∨ before (.capabilityMode region) = 2)
    (access : Memory.access? (before (.capabilityBase region)) (before (.capabilityLength region))
      (before (.register pointer)) displacement width.bytes = some address)
    (decoded : Memory.readByteWords? ((Memory.byteKeys address width.bytes).map before) = some bytes) :
    (∃ after, (loadRecipe ty width region destination pointer displacement address).guard
      ((loadRecipe ty width region destination pointer displacement address).inputs.map before)
      ((loadRecipe ty width region destination pointer displacement address).outputs.map after) = true) ∨
    (loadBooleanFailureRecipe ty width region pointer displacement address).guard
      ((loadBooleanFailureRecipe ty width region pointer displacement address).inputs.map before)
      ((loadBooleanFailureRecipe ty width region pointer displacement address).outputs.map before) = true := by
  cases value : checkedWord ty (packBytes bytes) with
  | none =>
      right
      obtain ⟨boolean, invalid⟩ := (checkedWord_none_iff ty (packBytes bytes)).mp value
      exact (load_boolean_failure_guard_iff ty width region pointer displacement address before before).mpr
        ⟨boolean, mode, access, bytes, decoded, invalid⟩
  | some result =>
      left
      refine ⟨Function.update before (.register destination) result,
        (load_guard_iff ty width region destination pointer displacement address before _).mpr
          ⟨mode, access, ?_⟩⟩
      simp [loadValue, decoded, value]

theorem load_bounds_exclusive (ty : TypeTag) (width : P1Source.Width) (region : Nat)
    (destination pointer : Reg) (displacement : Int) (address : Nat) (before after : Key → Word) :
    ¬ ((loadRecipe ty width region destination pointer displacement address).guard
          ((loadRecipe ty width region destination pointer displacement address).inputs.map before)
          ((loadRecipe ty width region destination pointer displacement address).outputs.map after) = true ∧
       (boundsFailureRecipe false width region pointer displacement).guard
          ((boundsFailureRecipe false width region pointer displacement).inputs.map before)
          ((boundsFailureRecipe false width region pointer displacement).outputs.map after) = true) := by
  rintro ⟨success, failed⟩
  have read := ((load_guard_iff ty width region destination pointer displacement address before after).mp success).2.1
  have noRead := ((bounds_failure_guard_iff false width region pointer displacement before after).mp failed).2
  rw [read] at noRead
  cases noRead

theorem load_boolean_exclusive (ty : TypeTag) (width : P1Source.Width) (region : Nat)
    (destination pointer : Reg) (displacement : Int) (address : Nat) (before after : Key → Word) :
    ¬ ((loadRecipe ty width region destination pointer displacement address).guard
          ((loadRecipe ty width region destination pointer displacement address).inputs.map before)
          ((loadRecipe ty width region destination pointer displacement address).outputs.map after) = true ∧
       (loadBooleanFailureRecipe ty width region pointer displacement address).guard
          ((loadBooleanFailureRecipe ty width region pointer displacement address).inputs.map before)
          ((loadBooleanFailureRecipe ty width region pointer displacement address).outputs.map after) = true) := by
  rintro ⟨success, failed⟩
  have result := ((load_guard_iff ty width region destination pointer displacement address before after).mp success).2.2
  obtain ⟨boolean, _, _, bytes, decoded, invalid⟩ :=
    (load_boolean_failure_guard_iff ty width region pointer displacement address before after).mp failed
  have noResult := (checkedWord_none_iff ty (packBytes bytes)).mpr ⟨boolean, invalid⟩
  simp only [loadValue, decoded, Option.bind_some, noResult] at result
  cases result

def addressFailureRecipe (region : Nat) (pointer : Reg) (index : Option Reg)
    (scale : Fin 4) (displacement : BitVec 32) : Recipe Key where
  inputs := Memory.capabilityKeys region ++ [.register pointer] ++ (index.toList.map Memory.Key.register)
  outputs := []
  guard := fun inputs outputs => match inputs with
    | base :: length :: mode :: pointer :: values => outputs.isEmpty &&
        (mode == 1 || mode == 2) &&
        ((indexValue? index values).bind (addressValue base length pointer scale displacement)).isNone
    | _ => false

theorem address_failure_guard_iff (region : Nat) (pointer : Reg) (index : Option Reg)
    (scale : Fin 4) (displacement : BitVec 32) (before after : Key → Word) :
    (addressFailureRecipe region pointer index scale displacement).guard
      ((addressFailureRecipe region pointer index scale displacement).inputs.map before)
      ((addressFailureRecipe region pointer index scale displacement).outputs.map after) = true ↔
      (before (.capabilityMode region) = 1 ∨ before (.capabilityMode region) = 2) ∧
      addressValue (before (.capabilityBase region)) (before (.capabilityLength region))
        (before (.register pointer)) scale displacement
        (match index with | none => 0 | some index => before (.register index)) = none := by
  cases index <;> simp [addressFailureRecipe, Memory.capabilityKeys, indexValue?, Bool.and_eq_true]


def memoryEdges? (instruction : Instr) (address activation : Nat) (point next invalid : Word) :
    Option (List (Control.Edge Key)) := do
  let success ← memoryRecipe? instruction address
  let failed ← match instruction with
    | .load ty width region _ pointer displacement => some [
         boundsFailureRecipe false width region.val pointer displacement.toInt,
         loadBooleanFailureRecipe ty width region.val pointer displacement.toInt address]
    | .loadFrame ty _ slot => some [loadBooleanFailureRecipe ty .word64 255 0 (8 * slot.val) address]
    | .store width region pointer displacement _ => some [boundsFailureRecipe true width region.val pointer displacement.toInt]
    | .address region _ pointer index scale displacement => some [addressFailureRecipe region.val pointer index scale displacement]
    | _ => none
  pure (⟨activation, point, next, success⟩ :: failed.map fun effect => ⟨activation, point, invalid, effect⟩)

def frameDisplacement (slot : Fin 24) : BitVec 32 := BitVec.ofNat 32 (8 * slot.val)

theorem frameDisplacement_toNat (slot : Fin 24) : (frameDisplacement slot).toNat = 8 * slot.val := by
  change (8 * slot.val) % 2 ^ 32 = 8 * slot.val
  exact Nat.mod_eq_of_lt (by have := slot.isLt; omega)

theorem frameDisplacement_toInt (slot : Fin 24) : (frameDisplacement slot).toInt = (8 * slot.val : Nat) := by
  rw [BitVec.toInt_eq_toNat_of_lt]
  · rw [frameDisplacement_toNat]
  · rw [frameDisplacement_toNat]
    have := slot.isLt
    omega

theorem frame_access (base : Word) (slot : Fin 24) (fits : base.toNat + 192 < 2 ^ 64) :
    Memory.access? base 192 base (8 * slot.val) 8 = some (base.toNat + 8 * slot.val) := by
  have within := slot.isLt
  have pointerLower : base.toNat ≤ base.toNat := le_rfl
  have pointerUpper : base.toNat ≤ base.toNat + (192#64).toNat := by simp
  have rangeFits : base.toNat + (192#64).toNat < 2 ^ 64 := by simpa using fits
  have equivalence := access?_iff_inside base 192 base (frameDisplacement slot) 8
    (base.toNat + 8 * slot.val) rangeFits pointerLower pointerUpper
  rw [frameDisplacement_toInt] at equivalence
  have lengthNat : (192 : Word).toNat = 192 := by decide
  rw [lengthNat] at equivalence
  apply equivalence.mpr
  constructor
  · omega
  · constructor
    · omega
    · omega

namespace Controls

theorem intermediate_escape_rejected :
    checkedAddress? ⟨100, 16⟩ 104 2 3 (-8) = some 112 ∧
      address? ⟨100, 16⟩ 104 2 3 (-8) = none := by decide

theorem negative_offset_inside : address? ⟨100, 16⟩ 112 0 0 (-8) = some 104 := by decide

theorem one_past_is_not_a_load :
    address? ⟨100, 16⟩ 112 1 2 0 = some 116 ∧ Memory.access? 100 16 116 0 1 = none := by decide

theorem noncanonical_bool_rejected : loadValue .boolean [2] = none := by decide

theorem bool_one_loaded : loadValue .boolean [1] = some 1 := by decide

theorem wide_i32_load_normalizes_low32 :
    loadValue .i32s [0, 0, 0, 128, 18, 52, 86, 120] = some 0xffffffff80000000 := by decide

theorem wide_u32_load_discards_high32 :
    loadValue .u32z [120, 86, 52, 18, 255, 255, 255, 255] = some 0x12345678 := by decide

theorem byte_into_i32_is_not_signed_byte :
    loadValue .i32s [128] = some 128 ∧ loadValue .i32s [128] ≠ some 0xffffffffffffff80 := by decide

private def byteState (value : Word) : Key → Word
  | .capabilityBase _ => 100
  | .capabilityLength _ => 1
  | .capabilityMode _ => 1
  | .register register => if register = 1 then 100 else 77
  | .byte address => if address = 100 then value else 0

theorem load_pointer_alias_fires :
    (profile [loadRecipe .u64 .byte 0 1 1 0 100]).theory.rewrites
      (encode {.capabilityBase 0, .capabilityLength 0, .capabilityMode 0, .register 1, .byte 100} (byteState 120))
      (encode {.capabilityBase 0, .capabilityLength 0, .capabilityMode 0, .register 1, .byte 100}
        (Function.update (byteState 120) (.register 1) 120)) := by
  apply (load_rewrite_iff _ _ _ _ _ _ _ _ _ _).mpr
  exact ⟨120, by decide, by decide, by decide, by decide, rfl⟩

private def booleanBefore : Control.Location Key → Word
  | .inl _ => 7
  | .inr key => byteState 2 key

private def booleanFailure : Control.Edge Key :=
  ⟨0, 7, 99, loadBooleanFailureRecipe .boolean .byte 0 1 0 100⟩

theorem loaded_bad_bool_fires_error :
    ∃ invocation : Invocation booleanFailure.recipe,
      CellEffects.system.Enables
        (encode {.inl 0, .inr (.capabilityBase 0), .inr (.capabilityLength 0),
          .inr (.capabilityMode 0), .inr (.register 1), .inr (.byte 100)} booleanBefore) invocation ∧
      CellEffects.system.fire
        (encode {.inl 0, .inr (.capabilityBase 0), .inr (.capabilityLength 0),
          .inr (.capabilityMode 0), .inr (.register 1), .inr (.byte 100)} booleanBefore) invocation =
        encode {.inl 0, .inr (.capabilityBase 0), .inr (.capabilityLength 0),
          .inr (.capabilityMode 0), .inr (.register 1), .inr (.byte 100)}
          (Function.update booleanBefore (.inl 0) 99) := by
  apply Control.Edge.readonly_realized booleanFailure rfl _ booleanBefore
    (Function.update booleanBefore (.inl 0) 99) <;> decide

private def boundsBefore : Control.Location Key → Word
  | .inl _ => 7
  | .inr (.register _) => 101
  | .inr key => byteState 120 key

private def boundsFailure : Control.Edge Key :=
  ⟨0, 7, 99, boundsFailureRecipe false .byte 0 1 0⟩

theorem bounds_error_without_any_byte_cell :
    ∃ invocation : Invocation boundsFailure.recipe,
      CellEffects.system.Enables
        (encode {.inl 0, .inr (.capabilityBase 0), .inr (.capabilityLength 0),
          .inr (.capabilityMode 0), .inr (.register 1)} boundsBefore) invocation ∧
      CellEffects.system.fire
        (encode {.inl 0, .inr (.capabilityBase 0), .inr (.capabilityLength 0),
          .inr (.capabilityMode 0), .inr (.register 1)} boundsBefore) invocation =
        encode {.inl 0, .inr (.capabilityBase 0), .inr (.capabilityLength 0),
          .inr (.capabilityMode 0), .inr (.register 1)}
          (Function.update boundsBefore (.inl 0) 99) := by
  apply Control.Edge.readonly_realized boundsFailure rfl _ boundsBefore
    (Function.update boundsBefore (.inl 0) 99) <;> decide

theorem malformed_byte_is_not_a_boolean_fault :
    (loadBooleanFailureRecipe .boolean .byte 0 1 0 100).guard [100, 1, 1, 100, 256] [] = false := by decide

theorem repeated_address_operand_is_one_read :
    (addressRecipe 0 2 1 (some 1) 0 0).reads.card = 4 := by decide

theorem readonly_store_not_enabled :
    (storeRecipe .word32 0 1 2 (-4) 100).guard [100, 8, 1, 104, 0x12345678] [120, 86, 52, 18] = false := by decide

theorem negative_store_offset_and_little_endian :
    (storeRecipe .word32 0 1 2 (-4) 100).guard [100, 8, 2, 104, 0x12345678] [120, 86, 52, 18] = true := by decide

end Controls


end Mettapedia.Machines.TIsa.P1Memory
