import Mettapedia.Machines.TIsa.X86P1Sub1Fuel
import Mettapedia.Machines.TIsa.X86BoundedLoad
import Mettapedia.Machines.TIsa.X86FrameLoadCapture

/-!
# Fused comparison and branch in the committed `sub1` image

Each captured guard is paired with its source comparison and both source arms.
The actual CMP and Jcc instructions realize the guard and preserve the fuel
allowance in RBP.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option Elab.async false

namespace Mettapedia.Machines.TIsa.X86P1Sub1Guards

open _root_.X86Registers X86Execution X86RegisterRefinement P1Capture P1Source
open X86P1Sub1Allowance (sub1 code_int)
local instance : MemoryPrimitives := X86Memory.ordinary

def compare (capacity : Bool) : Comparison := if capacity then .lessUnsigned else .equal

def failureCondition (capacity : Bool) : X86BranchCondition.Condition :=
  if capacity then .aboveEqual else .nonzero

structure Site where
  comparison : Span
  branch : Span
  capacity : Bool
  yes : Nat
  no : Nat
  noPath : List Nat
  deriving DecidableEq

private def firstAt (program : P1Capture.Program) (path : List Nat) : Option Nat :=
  (program.spans.find? (fun span => span.path.any (fun p => p.take path.length == path))).map Span.offset

def Site.decode? (program : P1Capture.Program) (branch : Span) : Option Site := do
  let path ← branch.path
  if path.getLast? != some 1 then none else
  let parent := path.dropLast
  let .seq (.seq _ (.instruction (.compare comparison .u64 7 6 (.register 8)))) (.branch condition _ failure) ←
    program.source.body.atPath parent | none
  if condition != 7 then none else
  let capacity ← match comparison with
    | .equal => some false
    | .lessUnsigned => some true
    | _ => none
  let comparison ← program.spans.find? (fun span =>
    span.kind == "CMP-FLAGS" && span.path == some (parent ++ [0, 1]))
  let displacement ← NativeImage.readRange? program.view (branch.offset + 2) 4
  let target := RelativeBranch.decodedTarget (branch.offset + 2) displacement
  if target < 0 then none else
  let targetSpan ← program.spans.find? (fun span => span.offset == target.toNat && span.kind == "IMM")
  let targetPath ← targetSpan.path
  -- Identical refusal arms can share the source path recorded in the capture.
  if targetPath.getLast? != some 0 || program.source.body.atPath targetPath.dropLast != some failure then none else
  return ⟨comparison, branch, capacity, ← firstAt program (path ++ [1]), target.toNat, targetPath.dropLast⟩

def Site.delta (site : Site) : Int := (site.no : Int) - site.yes

def Site.displacement (site : Site) : BitVec 32 := BitVec.ofInt 32 site.delta

def Site.bytes (site : Site) : List NativeImage.Byte :=
  [X86RegisterEncoding.rex true 0 10, 0x39, X86RegisterEncoding.modRM 0 10,
    0x0f, X86BranchCondition.opcode (failureCondition site.capacity)] ++
      (List.range 4).map (fun i => site.displacement.extractLsb' (8 * i) 8)

def Site.geometry (site : Site) (size : Nat) : Prop :=
  site.comparison.length = 3 ∧ site.branch.length = 6 ∧
    site.comparison.offset + 3 = site.branch.offset ∧ site.branch.offset + 6 = site.yes ∧
    site.yes < size ∧ site.no < size ∧ -(2 ^ 31 : Int) ≤ site.delta ∧ site.delta < (2 ^ 31 : Int)

def Site.checkOn (site : Site) (size : Nat) (view : NativeImage.View) : Bool :=
  letI : Decidable (site.geometry size) := by unfold Site.geometry; infer_instance
  decide (site.geometry size) && NativeImage.readRange? view site.comparison.offset 9 == some site.bytes

noncomputable def guards : List Span := sub1.spans.filter (fun span => span.kind == "IF-FLAGS")

noncomputable def sites : List Site := (guards.mapM (Site.decode? sub1)).getD []

theorem source_pairs : guards.mapM (Site.decode? sub1) = some sites := by kernel_reflexivity

theorem site_count : sites.length = 8 := by kernel_reflexivity

theorem compared_paths : sites.map (fun site => site.comparison) =
    sub1.spans.filter (fun span => span.kind == "CMP-FLAGS") := by kernel_reflexivity

theorem no_fund : sub1.source.body.fundPoints = 0 := by kernel_reflexivity

theorem sites_checked : sites.all (fun site => site.checkOn sub1.size sub1.view) = true := by
  kernel_reflexivity

noncomputable def site (index : Fin 8) : Site := sites[index.val]'(by rw [site_count]; exact index.isLt)

theorem checked (index : Fin 8) : (site index).checkOn sub1.size sub1.view = true :=
  List.all_eq_true.mp sites_checked _ (List.getElem_mem _)

theorem geometry (index : Fin 8) : (site index).geometry sub1.size := by
  have check := checked index
  simp only [Site.checkOn, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at check
  exact check.1

theorem captured_bytes (index : Fin 8) :
    NativeImage.readRange? sub1.view (site index).comparison.offset 9 = some (site index).bytes := by
  have check := checked index
  simp only [Site.checkOn, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at check
  exact check.2

theorem refusal_arm (index : Fin 8) :
    ((site index).branch.path.bind (fun path => sub1.source.body.atPath (path ++ [2]))) =
      sub1.source.body.atPath (site index).noPath := by
  fin_cases index <;> kernel_reflexivity

private theorem byte_at (index : Fin 8) (offset : Nat) (byte : NativeImage.Byte) (within : offset < 9)
    (present : (site index).bytes[offset]? = some byte) :
    sub1.view.read ((site index).comparison.offset + offset) = some byte :=
  X86CodePlacement.read_range_byte _ _ _ _ (captured_bytes index) offset byte within present

theorem bound_registers : X86BoundedLoad.physical 6 = 10 ∧ X86BoundedLoad.physical 8 = 0 := by decide

theorem failure_sense (capacity : Bool) (left right : Word) (flags : BitVec 32)
    (carry : Functions._get_rflagsbits_cf flags = Functions.bool_to_bits (left.toNat < right.toNat))
    (zero : Functions._get_rflagsbits_zf flags = Functions.zf_spec (left - right).toNat) :
    X86BranchCondition.value (failureCondition capacity) flags = !((compare capacity).evaluate left right) := by
  cases capacity with
  | false =>
    have same : (left - right).toNat = 0 ↔ left = right := by
      constructor
      · intro h
        have difference : left - right = 0#64 := BitVec.eq_of_toNat_eq h
        calc
          left = left - right + right := (BitVec.sub_add_cancel left right).symm
          _ = right := by simp [difference]
      · rintro rfl
        simp
    change ((0#1) == Functions._get_rflagsbits_zf flags) = !(left == right)
    rw [zero]
    by_cases h : left = right
    · subst right
      simp [Functions.zf_spec]
    · have different : ((left - right).toNat == 0) = false :=
        beq_eq_false_iff_ne.mpr (fun z => h (same.mp z))
      simp only [Functions.zf_spec, different, Bool.false_eq_true, ite_false, beq_self_eq_true,
        beq_eq_false_iff_ne.mpr h, Bool.not_false]
  | true =>
    change ((0#1) == Functions._get_rflagsbits_cf flags) = !decide (left.toNat < right.toNat)
    rw [carry, X86BranchCondition.unsigned_sense]
    by_cases h : left.toNat < right.toNat
    · simp [h, show ¬right.toNat ≤ left.toNat by omega]
    · simp [h, show right.toNat ≤ left.toNat by omega]

noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  X86BoundedLoad.handlers other extra

structure Entry (index : Fin 8) (state : State) where
  base : BitVec 48
  upper : base.toInt + sub1.size < (2 ^ 47 : Int)
  placed : X86CodePlacement.Placed state base.toInt sub1.view
  mode : X86PlainFetch.Facts state
  rip : state.regs.get? .rip = some ((address base.toInt (site index).comparison.offset).signExtend 64)
  left : Word
  right : Word
  leftKnown : lookup state 10 = some left
  rightKnown : lookup state 0 = some right
  flags : BitVec 32
  flagsKnown : state.regs.get? .rflags = some flags
  quiet : state.regs.get? .log_register_writes = some false

noncomputable def Entry.target {index : Fin 8} {state : State} (entry : Entry index state) : Nat :=
  if (compare (site index).capacity).evaluate entry.left entry.right then (site index).yes else (site index).no

set_option maxHeartbeats 4000000 in
theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (index : Fin 8) (state : State) (entry : Entry index state) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 2).run state = .ok () after ∧
      after.regs.get? .rip = some ((address entry.base.toInt entry.target).signExtend 64) ∧
      RegisterFrame {.rflags, .rip} state after ∧ lookup after 5 = lookup state 5 ∧
      after.regs.get? .rflags = some flags ∧ X86ControlFlags.Preserved state after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let guard := site index
  have geom := geometry index
  rcases geom with ⟨_, _, compareEnd, branchEnd, yesBound, noBound, low, high⟩
  have nextOffset : guard.comparison.offset + 9 = guard.yes := by
    change (site index).comparison.offset + 9 = (site index).yes
    omega
  have within (n : Nat) (h : n ≤ 9) : guard.comparison.offset + n ≤ sub1.size := by
    rw [← nextOffset] at yesBound
    omega
  let origin := X86P1Sub1Fuel.basis entry.base guard.comparison.offset entry.upper (within 3 (by decide))
    entry.mode entry.rip
  let window : X86LegacyFetch.Window state (0x39#8) true 0 10 := {
    toBasis := origin
    prefixByte := entry.placed _ _ (byte_at index 0 _ (by decide) rfl)
    opcodeByte := entry.placed _ _ (byte_at index 1 _ (by decide) rfl)
    modrmByte := entry.placed _ _ (byte_at index 2 _ (by decide) rfl) }
  obtain ⟨output, cmp, carry, zero⟩ := X86Comparison.fetched_compare64 (handlers other extra) vector state
    0 10 window entry.left entry.right entry.flags entry.rightKnown entry.leftKnown entry.flagsKnown entry.quiet
  let flags := X86Flags.mergeFlags entry.flags output
  let current := X86Move.putPointer (X86Flags.putFlags state flags) window.next
  have frame := X86Comparison.status_frame state flags window.next
  have flagsKnown : current.regs.get? .rflags = some flags := by
    simp [current, X86Move.putPointer, X86Flags.putFlags, Std.ExtDHashMap.get?_insert]
  have placed := X86CodePlacement.Placed.preserved _ _ entry.placed (X86StateFrame.registerOnly frame) (by simp)
  let atByte (n : Nat) := address entry.base.toInt (guard.comparison.offset + n)
  have atInt (n : Nat) (h : n ≤ 9) : (atByte n).toInt = entry.base.toInt + ((guard.comparison.offset + n : Nat) : Int) :=
    code_int entry.base entry.upper _ (within n h)
  have first : (atByte 3).toInt + 1 = (atByte 4).toInt := by rw [atInt 3 (by decide), atInt 4 (by decide)]; omega
  have second : (atByte 4).toInt + 1 = (atByte 5).toInt := by rw [atInt 4 (by decide), atInt 5 (by decide)]; omega
  have advance : (atByte 5).toInt + 4 = (atByte 9).toInt := by rw [atInt 5 (by decide), atInt 9 (by decide)]; omega
  let target := address entry.base.toInt guard.no
  have displacement : guard.displacement.toInt = guard.delta :=
    BitVec.toInt_ofInt_eq_self (by decide) low high
  have jump : target.toInt = (atByte 9).toInt + guard.displacement.toInt := by
    change (address entry.base.toInt guard.no).toInt = _
    rw [code_int entry.base entry.upper _ (Nat.le_of_lt noBound), atInt 9 (by decide), displacement, nextOffset]
    simp [Site.delta, guard]
  have bytes (j : Nat) (small : j < 4) :
      current.mem.get? ((address (atByte 5).toInt j).signExtend 52).toNat =
        some (guard.displacement.extractLsb' (8 * j) 8) := by
    have byte : guard.bytes[5 + j]? = some (guard.displacement.extractLsb' (8 * j) 8) := by
      unfold Site.bytes
      rw [List.getElem?_append_right (by simp)]
      simpa using congrArg (Option.map (fun k => guard.displacement.extractLsb' (8 * k) 8))
        (List.getElem?_range small)
    have observed := placed (guard.comparison.offset + (5 + j)) _ (byte_at index (5 + j) _ (by omega) byte)
    rw [atInt 5 (by decide)]
    simpa only [address, Int.natCast_add, Int.add_assoc] using observed
  let mode := entry.mode
  have branch := X86EscapeFetch.fetched_branch (X86Arithmetic.linkedHandlers (X86P1LoadBounds.baseHandlers other))
    extra vector (failureCondition guard.capacity) current (atByte 3) (atByte 4) (atByte 5) (atByte 9) target
    mode.control mode.attributes flags guard.displacement first second advance jump
    ((frame.registers .ms_reg (by decide)).trans mode.status)
    ((frame.registers .fault_reg (by decide)).trans mode.fault)
    ((frame.registers .msrs (by decide)).trans mode.msrs)
    ((frame.registers .seg_hidden_attrs (by decide)).trans mode.segments) mode.longMode mode.codeMode
    ((frame.registers .app_view (by decide)).trans mode.application)
    (X86FuelPrefix.pointer_rip _ _) flagsKnown
    ((frame.registers .log_register_writes (by decide)).trans entry.quiet)
    (placed _ _ (byte_at index 3 _ (by decide) rfl)) (placed _ _ (byte_at index 4 _ (by decide) rfl)) bytes
  let finish := if X86BranchCondition.value (failureCondition guard.capacity) flags then target else atByte 9
  let after := X86Move.putPointer current finish
  have route : finish = address entry.base.toInt entry.target := by
    have sense := failure_sense guard.capacity entry.left entry.right flags
      ((X86Comparison.merged_carry _ _).trans carry) ((X86Comparison.merged_zero _ _).trans zero)
    simp only [finish, sense, Entry.target, guard]
    cases (compare (site index).capacity).evaluate entry.left entry.right <;>
      simp [Bool.not_false, Bool.not_true, atByte, target, nextOffset, guard]
  have afterFrame : RegisterFrame {.rflags, .rip} state after := by
    apply (frame.trans (pointer_frame current finish)).mono
    simp
  have lastFrame := pointer_frame current finish
  have control := X86Bounds.merged_control state state entry.flags output window.next entry.flagsKnown
  exact ⟨after, flags, X86FuelPrefix.fetches_then 1 1 state current after
    (X86FuelPrefix.fetches_one _ _ cmp) (X86FuelPrefix.fetches_one _ _ branch),
    (X86FuelPrefix.pointer_rip _ _).trans (congrArg (fun a : BitVec 48 => some (a.signExtend 64)) route),
    afterFrame, afterFrame.lookup 5 (by decide), (lastFrame.registers .rflags (by decide)).trans flagsKnown,
    control.trans (X86ControlFlags.of_register_frame lastFrame (by decide))⟩

namespace Controls

theorem changed_condition :
    (site 0).checkOn sub1.size (X86P1Sub1Allowance.Controls.patch sub1.view ((site 0).comparison.offset + 4)) =
      false := by kernel_reflexivity

theorem changed_displacement :
    (site 0).checkOn sub1.size (X86P1Sub1Allowance.Controls.patch sub1.view ((site 0).comparison.offset + 5)) =
      false := by kernel_reflexivity

end Controls

namespace OperandLoads

open X86BoundedLoad

noncomputable def rejection : Option Nat := do
  let span ← sub1.spans.find? (fun span => span.kind == "FAILURE")
  let target := span.offset + 10
  if NativeImage.readRange? sub1.view target 5 == some [0xb8, 3, 0, 0, 0] then some target else none

theorem rejection_offset : rejection = some 1539 := by kernel_reflexivity

noncomputable def spans : List Span := sub1.spans.filter (fun span => span.kind == "LOAD")

theorem load_count : spans.length = 18 := by kernel_reflexivity

noncomputable def decode? (span : Span) : Option Instruction := do
  let reject ← rejection
  let path ← span.path
  let .instruction (.load .u64 .word64 region destination base offset) ← sub1.source.body.atPath path | none
  if valid : span.offset ≤ reject ∧ destination ≠ 0 ∧ (physical base).val % 8 ≠ 4 ∧
      (physical base).val % 8 ≠ 5 ∧ offset.toNat < 2 ^ 31 then
    some ⟨true, destination, base, region, ⟨offset.toNat, valid.2.2.2.2⟩, reject - span.offset,
      valid.2.1, valid.2.2.1, valid.2.2.2.1⟩
  else none

def source (code : Instruction) : Instr :=
  .load .u64 .word64 code.region code.destination code.base (displacement code)

def fits (span : Span) (code : Instruction) : Prop :=
  span.offset + span.length + 3 ≤ sub1.size ∧ span.length = (bytes code).length ∧
  span.offset + code.reject = 1539 ∧
  (X86Bounds.branchDelta (layout code) 23).toInt = (code.reject : Int) - 23 ∧
  (X86Bounds.branchDelta (layout code) (X86Bounds.compareAt (layout code))).toInt =
    (code.reject : Int) - X86Bounds.compareAt (layout code) ∧
  (X86Bounds.branchDelta (layout code) (X86Bounds.exitAt (layout code))).toInt =
    (code.reject : Int) - X86Bounds.exitAt (layout code)

noncomputable instance (span : Span) (code : Instruction) : Decidable (fits span code) :=
  inferInstanceAs (Decidable (_ ∧ _))

noncomputable def checkOn (span : Span) (view : NativeImage.View) : Bool :=
  match decode? span with
  | none => false
  | some code =>
    (decide (fits span code) && (span.path.bind sub1.source.body.atPath == some (.instruction (source code)))) &&
    NativeImage.readRange? view span.offset span.length == some ((bytes code).map (BitVec.ofNat 8))

theorem exact_loads : spans.all (fun span => checkOn span sub1.view) = true := by
  kernel_reflexivity

theorem captured (span : Span) (member : span ∈ spans) :
    ∃ code, decode? span = some code ∧ fits span code ∧
      (∃ path, span.path = some path ∧ sub1.source.body.atPath path = some (.instruction (source code))) ∧
      ∀ state base, X86CodePlacement.Placed state base sub1.view → codeLoaded state (base + span.offset) (bytes code) := by
  have checked := List.all_eq_true.mp exact_loads span member
  cases encoded : decode? span with
  | none => simp [checkOn, encoded] at checked
  | some code =>
    simp only [checkOn, encoded, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at checked
    obtain ⟨⟨valid, sourcePath⟩, read⟩ := checked
    refine ⟨code, rfl, valid, Option.bind_eq_some_iff.mp sourcePath, ?_⟩
    intro state base placed
    apply X86CodePlacement.range_code state base sub1.view span.offset (bytes code) placed
    simpa only [valid.2.1] using read

theorem changed_bounds_branch :
    checkOn (spans[0]'(by rw [load_count]; decide)) (X86P1Sub1Allowance.Controls.patch sub1.view 43) = false := by
  kernel_reflexivity

noncomputable def spanAt (index : Fin 18) : Span :=
  spans[index.val]'(by rw [load_count]; exact index.isLt)

theorem span_member (index : Fin 18) : spanAt index ∈ spans := List.getElem_mem _

private theorem hasInstruction (index : Fin 18) : (decode? (spanAt index)).isSome := by
  obtain ⟨code, accepted, _⟩ := captured _ (span_member index)
  rw [accepted]
  rfl

noncomputable def instructionAt (index : Fin 18) : Instruction :=
  (decode? (spanAt index)).get (hasInstruction index)

theorem instructionAt_spec (index : Fin 18) :
    fits (spanAt index) (instructionAt index) ∧
    (∃ path, (spanAt index).path = some path ∧
      sub1.source.body.atPath path = some (.instruction (source (instructionAt index)))) ∧
    ∀ state base, X86CodePlacement.Placed state base sub1.view →
      codeLoaded state (base + (spanAt index).offset) (bytes (instructionAt index)) := by
  obtain ⟨code, accepted, specification⟩ := captured _ (span_member index)
  have identified : instructionAt index = code := by
    unfold instructionAt
    simp [accepted]
  rw [identified]
  exact specification

structure Request (code : Instruction) (state : State) extends X86Bounds.Facts (layout code) state where
  within : (pointer - base).toNat + code.offset.val + (layout code).count.val ≤ length.toNat
  value : Word
  dataAddress : BitVec 48
  dataUpper : dataAddress.toInt + X86DataLoad.byteCount code.wide ≤ (2 ^ 47 : Int)
  effective : pointer + (displacement code).signExtend 64 = dataAddress.signExtend 64
  alignment : X86FrameLoad.alignmentEnabled controls flags visible = false ∨
    dataAddress &&& BitVec.ofNat 48 (X86DataLoad.byteCount code.wide - 1) = (0#48)
  dataBytes : ∀ index < X86DataLoad.byteCount code.wide,
    state.mem.get? ((address dataAddress.toInt index).signExtend 52).toNat =
      some (value.extractLsb' (8 * index) 8)

theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (index : Fin 18) (state : State) (base : BitVec 48)
    (upper : base.toInt + sub1.size < (2 ^ 47 : Int))
    (placed : X86CodePlacement.Placed state base.toInt sub1.view) (mode : X86PlainFetch.Facts state)
    (rip : state.regs.get? .rip = some ((address base.toInt (spanAt index).offset).signExtend 64))
    (request : Request (instructionAt index) state) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches (count (instructionAt index))).run state = .ok () after ∧
      RegisterFrame (writes (instructionAt index)) state after ∧
      lookup after (physical (instructionAt index).destination) =
        some (X86DataLoad.value (instructionAt index).wide request.value) ∧
      after.regs.get? .rip = some ((address base.toInt ((spanAt index).offset + (spanAt index).length)).signExtend 64) ∧
      after.regs.get? .rflags = some flags ∧ X86ControlFlags.Preserved state after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let span := spanAt index
  let code := instructionAt index
  obtain ⟨valid, _, loaded⟩ := instructionAt_spec index
  obtain ⟨spanFits, length, target, overflow, short, range⟩ := valid
  have inside : span.offset + 3 ≤ sub1.size := by
    change (spanAt index).offset + 3 ≤ sub1.size
    omega
  let origin := X86P1Sub1Fuel.basis base span.offset upper inside mode rip
  have located : origin.address.toInt = base.toInt + span.offset := code_int base upper _ (by omega)
  have upperBound : origin.address.toInt + (sub1.size - span.offset : Nat) < (2 ^ 47 : Int) := by
    rw [located, Nat.cast_sub (by omega)]
    omega
  have bytesFit : X86Bounds.exitAt (layout code) + 10 ≤ sub1.size - span.offset := by
    rw [bytes_length] at length
    change X86Bounds.exitAt (layout (instructionAt index)) + 10 ≤ sub1.size - (spanAt index).offset
    omega
  let bounds : X86Bounds.Context (layout code) origin.address :=
    { extent := sub1.size - span.offset
      upper := upperBound
      codeWithin := by have := bytesFit; omega
      rejectWithin := by
        have size := X86P1Sub1Allowance.exported_identity.2.2
        change (instructionAt index).reject ≤ _
        simp only [span] at *
        omega
      overflowDelta := overflow
      shortDelta := short
      rangeDelta := range }
  let input : X86BoundedLoad.Inputs code state origin :=
    { toFacts := request.toFacts
      geometry := bounds
      tailWithin := bytesFit
      loaded := by rw [located]; exact loaded state base.toInt placed }
  let data : X86BoundedLoad.Readable input :=
    { word := request.value
      dataAddress := request.dataAddress
      upper := request.dataUpper
      effective := request.effective
      safe := request.alignment
      present := request.dataBytes }
  obtain ⟨after, flags, run, frame, result, next, known, _, control, _⟩ :=
    X86BoundedLoad.succeeds other extra vector code state origin input request.within data
  refine ⟨after, flags, run, frame, result, ?_, known, control⟩
  rw [located, ← length] at next
  simpa only [address, Int.natCast_add, Int.add_assoc, span] using next

def Request.transport {code : Instruction} {before after : State} {writes : Finset Register}
    (request : Request code before) (frame : RegisterFrame writes before after)
    (pointerFixed : key (physical code.base) ∉ writes) (frameFixed : key 7 ∉ writes)
    (dataRegistersOnly : writes ⊆ dataRegisters)
    (control : X86ControlFlags.Preserved before after) (flags : BitVec 32)
    (known : after.regs.get? .rflags = some flags) : Request code after := by
  have ac := X86ControlFlags.ac_preserved control request.flags flags request.flagsKnown known
  refine { request with
    frameKnown := (frame.lookup 7 frameFixed).trans request.frameKnown
    pointerKnown := (frame.lookup _ pointerFixed).trans request.pointerKnown
    controlKnown := (frame.registers .ctrs (fun member => (by decide : Register.ctrs ∉ dataRegisters)
      (dataRegistersOnly member))).trans request.controlKnown
    visibleKnown := (frame.registers .seg_visibles (fun member => (by decide : Register.seg_visibles ∉ dataRegisters)
      (dataRegistersOnly member))).trans request.visibleKnown
    quiet := (frame.registers .log_register_writes (fun member =>
      (by decide : Register.log_register_writes ∉ dataRegisters) (dataRegistersOnly member))).trans request.quiet
    flags := flags
    flagsKnown := known
    alignment := by simpa only [X86FrameLoad.alignmentEnabled, ac] using request.alignment
    baseBytes := by intro i h; rw [frame.memory]; exact request.baseBytes i h
    lengthBytes := by intro i h; rw [frame.memory]; exact request.lengthBytes i h
    dataBytes := by intro i h; rw [frame.memory]; exact request.dataBytes i h }

end OperandLoads

namespace PremiseGuards

open OperandLoads (spanAt instructionAt Request)
open X86BoundedLoad (count physical writes)

def leftLoad (index : Fin 7) : Fin 18 := ⟨2 * index.val, by have := index.isLt; omega⟩
def rightLoad (index : Fin 7) : Fin 18 := ⟨2 * index.val + 1, by have := index.isLt; omega⟩
def guardIndex (index : Fin 7) : Fin 8 := ⟨index.val, by have := index.isLt; omega⟩

theorem layout (index : Fin 7) :
    (spanAt (leftLoad index)).offset + (spanAt (leftLoad index)).length = (spanAt (rightLoad index)).offset ∧
    (spanAt (rightLoad index)).offset + (spanAt (rightLoad index)).length = (site (guardIndex index)).comparison.offset ∧
    (instructionAt (leftLoad index)).wide = true ∧ (instructionAt (rightLoad index)).wide = true ∧
    physical (instructionAt (leftLoad index)).destination = 10 ∧
    physical (instructionAt (rightLoad index)).destination = 0 ∧ (site (guardIndex index)).capacity = false := by
  fin_cases index <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_reflexivity

theorem register_separation (index : Fin 7) :
    key (physical (instructionAt (rightLoad index)).base) ∉ writes (instructionAt (leftLoad index)) ∧
    key 7 ∉ writes (instructionAt (leftLoad index)) ∧ key 10 ∉ writes (instructionAt (rightLoad index)) ∧
    key 5 ∉ writes (instructionAt (leftLoad index)) ∧ key 5 ∉ writes (instructionAt (rightLoad index)) := by
  fin_cases index <;> exact of_decide_eq_true (by kernel_reflexivity)

theorem match_next (index : Fin 6) :
    (site (guardIndex ⟨index.val, by have := index.isLt; omega⟩)).yes =
      (spanAt (leftLoad ⟨index.val + 1, by have := index.isLt; omega⟩)).offset := by
  fin_cases index <;> kernel_reflexivity

theorem final_match : (site (guardIndex 6)).yes = 858 := by kernel_reflexivity

def modeAfterRegisters {before after : State} (mode : X86PlainFetch.Facts before)
    (preserves : ∀ r : Register, r ∉ dataRegisters → after.regs.get? r = before.regs.get? r) :
    X86PlainFetch.Facts after :=
  { mode with
    status := (preserves .ms_reg (by decide)).trans mode.status
    fault := (preserves .fault_reg (by decide)).trans mode.fault
    msrs := (preserves .msrs (by decide)).trans mode.msrs
    segments := (preserves .seg_hidden_attrs (by decide)).trans mode.segments
    application := (preserves .app_view (by decide)).trans mode.application }

def modeAfter {before after : State} {written : Finset Register}
    (mode : X86PlainFetch.Facts before) (frame : RegisterFrame written before after)
    (only : written ⊆ dataRegisters) : X86PlainFetch.Facts after :=
  modeAfterRegisters mode (fun r outside => frame.registers r (fun h => outside (only h)))

set_option maxHeartbeats 4000000 in
theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (index : Fin 7) (state : State) (base : BitVec 48) (upper : base.toInt + sub1.size < (2 ^ 47 : Int))
    (placed : X86CodePlacement.Placed state base.toInt sub1.view) (mode : X86PlainFetch.Facts state)
    (rip : state.regs.get? .rip = some ((address base.toInt (spanAt (leftLoad index)).offset).signExtend 64))
    (first : Request (instructionAt (leftLoad index)) state) (second : Request (instructionAt (rightLoad index)) state) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches
        (count (instructionAt (leftLoad index)) + count (instructionAt (rightLoad index)) + 2)).run state = .ok () after ∧
      after.regs.get? .rip = some ((address base.toInt
        (if first.value == second.value then (site (guardIndex index)).yes else (site (guardIndex index)).no)).signExtend 64) ∧
      RegisterFrame ((writes (instructionAt (leftLoad index)) ∪ writes (instructionAt (rightLoad index))) ∪
        {.rflags, .rip}) state after ∧
      lookup after 5 = lookup state 5 ∧ after.regs.get? .rflags = some flags ∧ X86ControlFlags.Preserved state after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨nextA, nextB, wideA, wideB, registerA, registerB, equalGuard⟩ := layout index
  obtain ⟨firstPointer, firstFrame, secondKeepsLeft, firstKeepsRbp, secondKeepsRbp⟩ := register_separation index
  obtain ⟨middle, middleFlags, loadA, frameA, left, atB, knownA, controlA⟩ :=
    OperandLoads.executes other extra vector (leftLoad index) state base upper placed mode rip first
  have dataA := X86BoundedLoad.writes_data (instructionAt (leftLoad index))
  have placedA := X86CodePlacement.Placed.preserved _ _ placed (X86StateFrame.registerOnly frameA) (by simp)
  let secondAtB := second.transport frameA firstPointer firstFrame dataA controlA middleFlags knownA
  obtain ⟨compared, comparedFlags, loadB, frameB, right, atCmp, knownB, controlB⟩ :=
    OperandLoads.executes other extra vector (rightLoad index) middle base upper placedA (modeAfter mode frameA dataA)
      (by simpa only [nextA] using atB) secondAtB
  have dataB := X86BoundedLoad.writes_data (instructionAt (rightLoad index))
  have joined := frameA.trans frameB
  have placedB := X86CodePlacement.Placed.preserved _ _ placed (X86StateFrame.registerOnly joined) (by simp)
  let entry : Entry (guardIndex index) compared :=
    { base := base
      upper := upper
      placed := placedB
      mode := modeAfter (modeAfter mode frameA dataA) frameB dataB
      rip := by simpa only [nextB] using atCmp
      left := first.value
      right := second.value
      leftKnown := (frameB.lookup 10 secondKeepsLeft).trans
        (by simpa only [registerA, wideA, X86DataLoad.value, ite_true] using left)
      rightKnown := by simpa only [registerB, wideB, X86DataLoad.value, ite_true, secondAtB, Request.transport] using right
      flags := comparedFlags
      flagsKnown := knownB
      quiet := (frameB.registers .log_register_writes (fun h =>
        (by decide : Register.log_register_writes ∉ dataRegisters) (dataB h))).trans
        ((frameA.registers .log_register_writes (fun h =>
          (by decide : Register.log_register_writes ∉ dataRegisters) (dataA h))).trans first.quiet) }
  obtain ⟨after, flags, guarded, pc, guardFrame, rbp, afterFlags, controlC⟩ :=
    X86P1Sub1Guards.executes other extra vector (guardIndex index) compared entry
  refine ⟨after, flags, X86FuelPrefix.fetches_then _ 2 state compared after
    (X86FuelPrefix.fetches_then _ _ state middle compared loadA loadB) guarded,
    ?_, joined.trans guardFrame, (rbp.trans (frameB.lookup 5 secondKeepsRbp)).trans
      (frameA.lookup 5 firstKeepsRbp), afterFlags, (controlA.trans controlB).trans controlC⟩
  simpa only [entry, Entry.target, equalGuard, compare, Comparison.evaluate, Bool.false_eq_true, ite_false] using pc

abbrev prefixWrites : Finset Register := {.rax, .r10, .r14, .r15, .rflags, .rip}

theorem pair_writes (index : Fin 7) :
    (writes (instructionAt (leftLoad index)) ∪ writes (instructionAt (rightLoad index))) ∪ {.rflags, .rip} ⊆
      prefixWrites := by
  fin_cases index <;> exact of_decide_eq_true (by kernel_reflexivity)

theorem operand_pointers_fixed (index : Fin 7) :
    key (physical (instructionAt (leftLoad index)).base) ∉ prefixWrites ∧
    key (physical (instructionAt (rightLoad index)).base) ∉ prefixWrites := by
  fin_cases index <;> exact of_decide_eq_true (by kernel_reflexivity)

noncomputable def entryOffset (n : Nat) : Nat :=
  if valid : n < 7 then (spanAt (leftLoad ⟨n, valid⟩)).offset else 858

noncomputable def pairCount (n : Nat) : Nat :=
  if valid : n < 7 then
    count (instructionAt (leftLoad ⟨n, valid⟩)) + count (instructionAt (rightLoad ⟨n, valid⟩)) + 2
  else 0

noncomputable def prefixCount : Nat → Nat
  | 0 => 0
  | n + 1 => prefixCount n + pairCount n

theorem matched_target (index : Fin 7) :
    (site (guardIndex index)).yes = entryOffset (index.val + 1) := by
  fin_cases index <;> kernel_reflexivity

set_option maxHeartbeats 4000000 in
theorem executes_matching_prefix (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : BitVec 48)
    (upper : base.toInt + sub1.size < (2 ^ 47 : Int))
    (placed : X86CodePlacement.Placed state base.toInt sub1.view) (mode : X86PlainFetch.Facts state)
    (rip : state.regs.get? .rip = some ((address base.toInt (entryOffset 0)).signExtend 64))
    (left : ∀ i, Request (instructionAt (leftLoad i)) state)
    (right : ∀ i, Request (instructionAt (rightLoad i)) state)
    (n : Nat) (within : n ≤ 7)
    (agrees : ∀ i : Fin 7, i.val < n → (left i).value == (right i).value) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches (prefixCount n)).run state = .ok () after ∧
      after.regs.get? .rip = some ((address base.toInt (entryOffset n)).signExtend 64) ∧
      RegisterFrame prefixWrites state after ∧ after.regs.get? .rflags = some flags ∧
      X86ControlFlags.Preserved state after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  induction n with
  | zero =>
    exact ⟨state, (left 0).flags, X86FuelPrefix.fetches_zero state, rip,
      RegisterFrame.refl _ state, (left 0).flagsKnown, X86ControlFlags.Preserved.refl _⟩
  | succ n ih =>
    obtain ⟨middle, flags, before, atNext, frame, flagsKnown, control⟩ :=
      ih (by omega) (fun i h => agrees i (by omega))
    let index : Fin 7 := ⟨n, by omega⟩
    have dataOnly : prefixWrites ⊆ dataRegisters := by decide
    obtain ⟨leftFixed, rightFixed⟩ := operand_pointers_fixed index
    let loadedLeft := (left index).transport frame leftFixed (by decide) dataOnly control flags flagsKnown
    let loadedRight := (right index).transport frame rightFixed (by decide) dataOnly control flags flagsKnown
    have current : middle.regs.get? .rip = some ((address base.toInt (spanAt (leftLoad index)).offset).signExtend 64) := by
      unfold entryOffset at atNext
      simpa only [dif_pos index.isLt, index] using atNext
    have code := X86CodePlacement.Placed.preserved _ _ placed (X86StateFrame.registerOnly frame) (by simp)
    obtain ⟨after, afterFlags, guarded, pc, stepFrame, _, known, controlStep⟩ :=
      executes other extra vector index middle base upper code (modeAfter mode frame dataOnly) current loadedLeft loadedRight
    have matchValue : (loadedLeft.value == loadedRight.value) = true := agrees index (by change n < n + 1; omega)
    have afterPc : after.regs.get? .rip = some ((address base.toInt (entryOffset (n + 1))).signExtend 64) := by
      rw [pc, matchValue, if_pos rfl, matched_target]
    have stepCount : (X86FuelPrefix.fetches (pairCount n)).run middle = .ok () after := by
      unfold pairCount
      simpa only [dif_pos index.isLt, index] using guarded
    exact ⟨after, afterFlags, X86FuelPrefix.fetches_then (prefixCount n) (pairCount n) state middle after before stepCount,
      afterPc, by simpa only [Finset.union_self] using frame.trans (stepFrame.mono (pair_writes index)), known,
      control.trans controlStep⟩

end PremiseGuards

namespace Capacity

open X86FrameLoadCapture (expected physical displacement)

private def offset (limit : Bool) : Nat := if limit then 865 else 858
private def destination (limit : Bool) : Fin 14 := if limit then 8 else 6
private def field (limit : Bool) : Fin 24 := if limit then 23 else 22

private noncomputable def sourceAt (start : Nat) : Option Stmt := do
  let span ← sub1.spans.find? (fun span => span.offset == start && span.kind == "LOAD-FRAME")
  sub1.source.body.atPath (← span.path)

theorem source_fields :
    sourceAt 858 = some (.instruction (.loadFrame .u64 6 22)) ∧
    sourceAt 865 = some (.instruction (.loadFrame .u64 8 23)) := by
  constructor <;> kernel_reflexivity

private def loadBytes (limit : Bool) : List Nat :=
  expected (destination limit) (8 * (field limit).val)

theorem bytes_checked (limit : Bool) :
    NativeImage.readRange? sub1.view (offset limit) (loadBytes limit).length =
      some ((loadBytes limit).map (BitVec.ofNat 8)) := by
  cases limit <;> kernel_reflexivity

theorem guard_layout :
    (site 7).comparison.offset = 872 ∧ (site 7).capacity = true ∧
    (site 7).yes = 881 ∧ (site 7).no = 1305 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> kernel_reflexivity

theorem changed_field :
    NativeImage.readRange? (X86P1Sub1Allowance.Controls.patch sub1.view 861) 858
      (loadBytes false).length ≠ some ((loadBytes false).map (BitVec.ofNat 8)) :=
  of_decide_eq_true (by kernel_reflexivity)

structure Inputs (state : State) where
  frame : Word
  frameKnown : lookup state 7 = some frame
  controls : Vector (BitVec 64) 17
  controlsKnown : state.regs.get? .ctrs = some controls
  visible : Vector (BitVec 16) 6
  visibleKnown : state.regs.get? .seg_visibles = some visible
  flags : BitVec 32
  flagsKnown : state.regs.get? .rflags = some flags
  quiet : state.regs.get? .log_register_writes = some false
  data : Bool → BitVec 48
  value : Bool → Word
  upper : ∀ limit, (data limit).toInt + 8 ≤ (2 ^ 47 : Int)
  effective : ∀ limit, frame + (displacement (field limit)).signExtend 64 = (data limit).signExtend 64
  aligned : ∀ limit, data limit &&& (7#48) = 0#48
  present : ∀ limit index, index < 8 →
    state.mem.get? ((address (data limit).toInt index).signExtend 52).toNat =
      some ((value limit).extractLsb' (8 * index) 8)

def Inputs.transport {before after : State} {written : Finset Register} (input : Inputs before)
    (framed : RegisterFrame written before after) (frameFixed : key 7 ∉ written)
    (dataOnly : written ⊆ dataRegisters) (flags : BitVec 32)
    (flagsKnown : after.regs.get? .rflags = some flags) : Inputs after :=
  let preserves (reg : Register) (outside : reg ∉ dataRegisters) :=
    framed.registers reg (fun h => outside (dataOnly h))
  { input with
    frameKnown := (framed.lookup 7 frameFixed).trans input.frameKnown
    controlsKnown := (preserves .ctrs (by decide)).trans input.controlsKnown
    visibleKnown := (preserves .seg_visibles (by decide)).trans input.visibleKnown
    flags := flags
    flagsKnown := flagsKnown
    quiet := (preserves .log_register_writes (by decide)).trans input.quiet
    present := by intro limit index within; rw [framed.memory]; exact input.present limit index within }

private def afterLoad (limit : Bool) (state : State) (base : BitVec 48) (value : Word) : State :=
  X86Move.putPointer (put state (physical (destination limit)) value) (address base.toInt (offset limit + 7))

private theorem load_frame (limit : Bool) (state : State) (base : BitVec 48) (value : Word) :
    RegisterFrame {key (physical (destination limit)), .rip} state (afterLoad limit state base value) :=
  (put_frame _ _ _).trans (pointer_frame _ _)

theorem loads (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (limit : Bool) (state : State) (base : BitVec 48) (upper : base.toInt + sub1.size < (2 ^ 47 : Int))
    (placed : X86CodePlacement.Placed state base.toInt sub1.view) (mode : X86PlainFetch.Facts state)
    (rip : state.regs.get? .rip = some ((address base.toInt (offset limit)).signExtend 64)) (input : Inputs state) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state = .ok () (afterLoad limit state base (input.value limit)) := by
  have fits : offset limit + 7 ≤ sub1.size := by
    rw [X86P1Sub1Allowance.exported_identity.2.2]
    cases limit <;> decide
  let origin := X86P1Sub1Fuel.basis base (offset limit) upper (by omega) mode rip
  have advance : origin.next.toInt + 4 = (address base.toInt (offset limit + 7)).toInt := by
    change (address base.toInt (offset limit + 3)).toInt + 4 = _
    rw [code_int base upper _ (by omega), code_int base upper _ fits]
    omega
  obtain ⟨sample, member, args⟩ := X86FrameLoadCapture.sample_present (destination limit) (field limit)
  have bytes := X86FrameLoadCapture.checked_bytes _ _ sample member args
  have loaded : X86Execution.codeLoaded state origin.address.toInt sample.bytes := by
    rw [bytes]
    exact X86CodePlacement.code_of_read_range state base.toInt sub1.view (offset limit) origin.address
      (loadBytes limit) (code_int base upper _ (by omega)) placed (bytes_checked limit)
  have run := X86FrameLoadCapture.captured_executes (handlers other extra) vector _ _ sample member args
    state origin (address base.toInt (offset limit + 7)) (input.data limit) input.visible input.controls
    input.frame (input.value limit) input.flags advance (input.upper limit) input.frameKnown
    input.controlsKnown input.flagsKnown input.visibleKnown input.quiet (input.effective limit)
    (input.aligned limit) loaded (input.present limit)
  rw [X86BoundedLoad.load_handlers] at run
  exact run

theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (base : BitVec 48) (upper : base.toInt + sub1.size < (2 ^ 47 : Int))
    (placed : X86CodePlacement.Placed state base.toInt sub1.view) (mode : X86PlainFetch.Facts state)
    (rip : state.regs.get? .rip = some ((address base.toInt 858).signExtend 64)) (input : Inputs state) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 4).run state = .ok () after ∧
      after.regs.get? .rip = some ((address base.toInt
        (if (input.value false).toNat < (input.value true).toNat then 881 else 1305)).signExtend 64) ∧
      RegisterFrame {.r10, .rax, .rflags, .rip} state after ∧ lookup after 5 = lookup state 5 ∧
      after.regs.get? .rflags = some flags ∧ X86ControlFlags.Preserved state after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let middle := afterLoad false state base (input.value false)
  have first := loads other extra vector false state base upper placed mode rip input
  have frameA : RegisterFrame {.r10, .rip} state middle := load_frame false state base (input.value false)
  have placedA := X86CodePlacement.Placed.preserved _ _ placed (X86StateFrame.registerOnly frameA) (by simp)
  let modeA := PremiseGuards.modeAfter mode frameA (by decide)
  let nextInput := input.transport frameA (by decide) (by decide) input.flags
    ((frameA.registers .rflags (by decide)).trans input.flagsKnown)
  have second := loads other extra vector true middle base upper placedA modeA
    (X86FuelPrefix.pointer_rip _ _) nextInput
  let compared := afterLoad true middle base (input.value true)
  have frameB : RegisterFrame {.rax, .rip} middle compared := load_frame true middle base (input.value true)
  have joined := frameA.trans frameB
  have placedB := X86CodePlacement.Placed.preserved _ _ placed (X86StateFrame.registerOnly joined) (by simp)
  let entry : Entry 7 compared :=
    { base := base
      upper := upper
      placed := placedB
      mode := PremiseGuards.modeAfter modeA frameB (by decide)
      rip := by rw [guard_layout.1]; exact X86FuelPrefix.pointer_rip _ _
      left := input.value false
      right := input.value true
      leftKnown := (frameB.lookup 10 (by decide)).trans (by
        simp only [middle, afterLoad, X86Move.lookup_putPointer]; exact lookup_put_same _ _ _)
      rightKnown := by simp only [compared, afterLoad, X86Move.lookup_putPointer]; exact lookup_put_same _ _ _
      flags := input.flags
      flagsKnown := (joined.registers .rflags (by decide)).trans input.flagsKnown
      quiet := (joined.registers .log_register_writes (by decide)).trans input.quiet }
  obtain ⟨after, flags, guard, target, frameC, _, known, control⟩ :=
    X86P1Sub1Guards.executes other extra vector 7 compared entry
  have framed : RegisterFrame {.r10, .rax, .rflags, .rip} state after :=
    (joined.trans frameC).mono (by decide)
  refine ⟨after, flags, X86FuelPrefix.fetches_then 2 2 state compared after
    (X86FuelPrefix.fetches_then 1 1 state middle compared
      (X86FuelPrefix.fetches_one _ _ first) (X86FuelPrefix.fetches_one _ _ second)) guard,
    ?_, framed, framed.lookup 5 (by decide), known,
    (X86ControlFlags.of_register_frame joined (by decide)).trans control⟩
  simpa only [Entry.target, entry, guard_layout.2.1, guard_layout.2.2.1, guard_layout.2.2.2,
    compare, ite_true, Comparison.evaluate, decide_eq_true_eq, BitVec.lt_def] using target

open PremiseGuards (leftLoad rightLoad entryOffset prefixCount prefixWrites)
open OperandLoads (instructionAt Request)

theorem executes_after_matches (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : BitVec 48)
    (upper : base.toInt + sub1.size < (2 ^ 47 : Int))
    (placed : X86CodePlacement.Placed state base.toInt sub1.view) (mode : X86PlainFetch.Facts state)
    (rip : state.regs.get? .rip = some ((address base.toInt (entryOffset 0)).signExtend 64))
    (left : ∀ i, Request (instructionAt (leftLoad i)) state)
    (right : ∀ i, Request (instructionAt (rightLoad i)) state)
    (agrees : ∀ i : Fin 7, (left i).value == (right i).value) (input : Inputs state) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches (prefixCount 7 + 4)).run state = .ok () after ∧
      after.regs.get? .rip = some ((address base.toInt
        (if (input.value false).toNat < (input.value true).toNat then 881 else 1305)).signExtend 64) ∧
      RegisterFrame prefixWrites state after ∧ lookup after 5 = lookup state 5 ∧
      after.regs.get? .rflags = some flags ∧ X86ControlFlags.Preserved state after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle, flags, premisesRun, atLimit, frame, known, control⟩ :=
    PremiseGuards.executes_matching_prefix other extra vector state base upper placed mode rip left right 7
      (by decide) (fun i _ => agrees i)
  have dataOnly : prefixWrites ⊆ dataRegisters := by decide
  let current := input.transport frame (by decide) dataOnly flags known
  have code := X86CodePlacement.Placed.preserved _ _ placed (X86StateFrame.registerOnly frame) (by simp)
  obtain ⟨after, finishFlags, step, pc, written, rbp, flagsKnown, controlStep⟩ :=
    executes other extra vector middle base upper code (PremiseGuards.modeAfter mode frame dataOnly)
      (by simpa only [entryOffset, dif_neg (show ¬(7 : Nat) < 7 by decide)] using atLimit) current
  have combined : RegisterFrame prefixWrites state after := (frame.trans written).mono (by decide)
  exact ⟨after, finishFlags, X86FuelPrefix.fetches_then _ 4 state middle after premisesRun step, pc,
    combined, rbp.trans (frame.lookup 5 (by decide)), flagsKnown, control.trans controlStep⟩

end Capacity

namespace FirstGuard

open OperandLoads (spanAt instructionAt Request)
open X86BoundedLoad (count physical writes)

theorem layout : (spanAt 0).offset = 24 ∧
    (spanAt 0).offset + (spanAt 0).length = (spanAt 1).offset ∧
    (spanAt 1).offset + (spanAt 1).length = (site 0).comparison.offset ∧
    count (instructionAt 0) = 10 ∧ count (instructionAt 1) = 10 ∧
    (instructionAt 0).wide = true ∧ (instructionAt 1).wide = true ∧
    physical (instructionAt 0).destination = 10 ∧ physical (instructionAt 1).destination = 0 ∧
    (site 0).capacity = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_reflexivity

theorem register_separation : key (physical (instructionAt 1).base) ∉ writes (instructionAt 0) ∧
    key 7 ∉ writes (instructionAt 0) ∧ key 10 ∉ writes (instructionAt 1) ∧
    key 5 ∉ writes (instructionAt 0) ∧ key 5 ∉ writes (instructionAt 1) :=
  PremiseGuards.register_separation 0

theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (base : BitVec 48) (upper : base.toInt + sub1.size < (2 ^ 47 : Int))
    (placed : X86CodePlacement.Placed state base.toInt sub1.view) (mode : X86PlainFetch.Facts state)
    (rip : state.regs.get? .rip = some ((address base.toInt 24).signExtend 64))
    (first : Request (instructionAt 0) state) (second : Request (instructionAt 1) state) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 22).run state = .ok () after ∧
      after.regs.get? .rip = some ((address base.toInt
        (if first.value == second.value then (site 0).yes else (site 0).no)).signExtend 64) ∧
      RegisterFrame ((writes (instructionAt 0) ∪ writes (instructionAt 1)) ∪ {.rflags, .rip}) state after ∧
      lookup after 5 = lookup state 5 ∧ after.regs.get? .rflags = some flags ∧ X86ControlFlags.Preserved state after := by
  obtain ⟨start, _, _, countA, countB, _, _, _, _, _⟩ := layout
  have run := PremiseGuards.executes other extra vector 0 state base upper placed mode
    (by change state.regs.get? .rip = some ((address base.toInt (spanAt 0).offset).signExtend 64)
        rw [start]; exact rip) first second
  have leftIndex : PremiseGuards.leftLoad 0 = 0 := by decide
  have rightIndex : PremiseGuards.rightLoad 0 = 1 := by decide
  have comparisonIndex : PremiseGuards.guardIndex 0 = 0 := by decide
  simpa only [leftIndex, rightIndex, comparisonIndex, countA, countB] using run

end FirstGuard

end Mettapedia.Machines.TIsa.X86P1Sub1Guards

#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.source_pairs
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.site_count
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.compared_paths
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.no_fund
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.sites_checked
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.refusal_arm
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.failure_sense
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.executes
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.Controls.changed_condition
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.Controls.changed_displacement
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.OperandLoads.rejection_offset
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.OperandLoads.load_count
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.OperandLoads.exact_loads
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.OperandLoads.captured
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.OperandLoads.changed_bounds_branch
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.OperandLoads.instructionAt_spec
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.OperandLoads.executes
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.OperandLoads.Request.transport
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.Capacity.source_fields
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.Capacity.bytes_checked
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.Capacity.changed_field
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.Capacity.loads
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.Capacity.executes
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.Capacity.executes_after_matches
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.PremiseGuards.layout
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.PremiseGuards.register_separation
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.PremiseGuards.match_next
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.PremiseGuards.final_match
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.PremiseGuards.executes
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.PremiseGuards.matched_target
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.PremiseGuards.executes_matching_prefix
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.FirstGuard.layout
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.FirstGuard.register_separation
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Guards.FirstGuard.executes
