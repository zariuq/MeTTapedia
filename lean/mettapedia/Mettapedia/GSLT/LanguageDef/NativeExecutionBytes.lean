import Mettapedia.GSLT.LanguageDef.NativeExecutionScope
import Mettapedia.GSLT.LanguageDef.NativeOpsByteViews

/-!
Byte comparisons at the native execution interface. A scope lookup precedes
all payload reads. Comparisons reject null nonempty views and unequal lengths
without dereferencing them; a byte mismatch stops the remaining reads.
Source cells and target cells are inspected independently. Storage that is
actually read must be live and byte-typed. Concrete addresses and buffer
strides remain a pointer-realization obligation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeExecutionBytes

open NativeOps (Address SourceMemory TargetMemory SourceValue TargetValue MemoryRelated encodeValue)
open NativeExecutionScope

theorem byte_beq_decide (left right : UInt8) :
    (left == right) = decide (left = right) := rfl

theorem byte_beq_true (left right : UInt8) (equal : left = right) :
    (left == right) = true := by
  rw [byte_beq_decide]
  exact decide_eq_true equal

theorem byte_beq_false (left right : UInt8) (different : left ≠ right) :
    (left == right) = false := by
  rw [byte_beq_decide]
  exact decide_eq_false different

theorem byte_list_beq_true_iff (left right : List UInt8) :
    (left == right) = true ↔ left = right := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons _ _ => constructor <;> intro impossible <;> cases impossible
  | cons byte rest ih =>
    cases right with
    | nil => constructor <;> intro impossible <;> cases impossible
    | cons expected tail =>
      simp only [List.cons_beq_cons, Bool.and_eq_true, byte_beq_decide,
        decide_eq_true_eq, ih, List.cons.injEq]

theorem byte_list_beq_false (left right : List UInt8) (different : left ≠ right) :
    (left == right) = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  exact different ((byte_list_beq_true_iff left right).mp accepted)

theorem byte_list_beq_comm (left right : List UInt8) :
    (left == right) = (right == left) := by
  apply Bool.eq_iff_iff.mpr
  rw [byte_list_beq_true_iff, byte_list_beq_true_iff]
  exact eq_comm

def sourceCompare (memory : SourceMemory) (address : Address) : List UInt8 → Option Bool
  | [] => some true
  | expected :: rest => do
      let actual ← NativeOps.ByteViews.sourceAt memory address
      if actual = expected then sourceCompare memory (NativeOps.ByteViews.advance address) rest
      else some false

def targetCompare (memory : TargetMemory) (address : Address) : List UInt8 → Option Bool
  | [] => some true
  | expected :: rest =>
      match NativeOps.ByteViews.targetAt memory address with
      | none => none
      | some actual =>
        if actual == expected then targetCompare memory (NativeOps.ByteViews.advance address) rest
        else some false

theorem compare_correspondence (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (address : Address) (expected : List UInt8) :
    targetCompare target address expected = sourceCompare source address expected := by
  induction expected generalizing address with
  | nil => rfl
  | cons byte rest ih =>
    simp only [targetCompare, sourceCompare,
      NativeOps.ByteViews.byte_cell_correspondence source target related]
    cases first : NativeOps.ByteViews.sourceAt source address with
    | none => rfl
    | some actual =>
      simp only [bind, Option.bind_some, beq_iff_eq]
      by_cases same : actual = byte
      · simp only [same, if_true, ih]
      · simp only [same, if_false]

def sourceEqual (memory : SourceMemory) (view : SourceValue)
    (expected : List UInt8) : Option Bool :=
  match view with
  | .array .byte address length =>
    match address with
    | none => some (decide (length.val = 0 ∧ expected = []))
    | some base =>
      if length.val = expected.length then sourceCompare memory base expected
      else some false
  | _ => none

def targetEqual (memory : TargetMemory) (view : TargetValue)
    (expected : List UInt8) : Option Bool :=
  match view with
  | .array .byte address length =>
    if length = 0 then some expected.isEmpty
    else match address with
      | none => some false
      | some base =>
        if length.toNat = expected.length then targetCompare memory base expected
        else some false
  | _ => none

theorem equal_correspondence (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (view : SourceValue) (expected : List UInt8) :
    targetEqual target (encodeValue view) expected = sourceEqual source view expected := by
  cases view <;> try rfl
  case array element address length =>
    cases element <;> try rfl
    simp only [targetEqual, sourceEqual, encodeValue, NativeWord64.encode_eq_zero,
      NativeWord64.encode_toNat]
    by_cases empty : length.val = 0
    · simp only [empty, if_true]
      cases address with
      | none => cases expected <;> rfl
      | some base => cases expected <;> rfl
    · simp only [empty, if_false]
      cases address with
      | none => simp
      | some base => simp only [compare_correspondence source target related]

theorem compare_with_contents (memory : SourceMemory) (address : Address)
    (actual expected : List UInt8) (sameLength : actual.length = expected.length)
    (read : NativeOps.ByteViews.sourceBlock memory address actual.length = some actual) :
    sourceCompare memory address expected = some (actual == expected) := by
  induction expected generalizing address actual with
  | nil =>
    have empty : actual = [] := List.eq_nil_of_length_eq_zero sameLength
    rw [empty]
    rfl
  | cons expected rest ih =>
    cases actual with
    | nil => cases sameLength
    | cons first tail =>
      have length : tail.length = rest.length := Nat.succ.inj sameLength
      cases cell : NativeOps.ByteViews.sourceAt memory address with
      | none => simp [NativeOps.ByteViews.sourceBlock, cell, bind, Option.bind] at read
      | some byte =>
        cases next : NativeOps.ByteViews.sourceBlock memory (NativeOps.ByteViews.advance address) tail.length with
        | none => simp [NativeOps.ByteViews.sourceBlock, cell, next, bind, Option.bind] at read
        | some bytes =>
          have equal : byte :: bytes = first :: tail := by
            apply Option.some.inj
            simpa only [List.length_cons, NativeOps.ByteViews.sourceBlock, cell, next,
              bind, Option.bind] using read
          obtain ⟨head, remaining⟩ := List.cons.inj equal
          subst byte
          subst bytes
          simp only [sourceCompare, cell, bind, Option.bind_some]
          by_cases same : first = expected
          · simp only [same, if_true, ih _ _ length next, List.cons_beq_cons,
              byte_beq_true expected expected rfl, Bool.true_and]
          · simp only [same, if_false, List.cons_beq_cons,
              byte_beq_false first expected same, Bool.false_and]

theorem equal_with_contents (memory : SourceMemory) (view : SourceValue)
    (actual expected : List UInt8) (read : NativeOps.ByteViews.sourceView memory view = some actual) :
    sourceEqual memory view expected = some (actual == expected) := by
  cases view <;> try cases read
  case array element address length =>
    cases element <;> try cases read
    have lengthOf := NativeOps.ByteViews.source_view_length memory address length actual read
    cases address with
    | none =>
      by_cases empty : length.val = 0
      · have emptyActual : actual = [] := List.eq_nil_of_length_eq_zero (lengthOf.trans empty)
        subst actual
        simp only [sourceEqual, empty]
        cases expected <;> rfl
      · simp [NativeOps.ByteViews.sourceView, empty] at read
    | some base =>
      by_cases sameLength : length.val = expected.length
      · have block : NativeOps.ByteViews.sourceBlock memory base actual.length = some actual := by
          by_cases empty : length.val = 0
          · have emptyActual : actual = [] := List.eq_nil_of_length_eq_zero (lengthOf.trans empty)
            subst actual
            rfl
          · simpa only [NativeOps.ByteViews.sourceView, empty, if_false, Option.bind_some, lengthOf]
              using read
        simp only [sourceEqual, sameLength, if_true]
        exact compare_with_contents memory base actual expected (lengthOf.trans sameLength) block
      · have different : (actual == expected) = false := by
          apply byte_list_beq_false
          intro same
          exact sameLength (lengthOf.symm.trans (congrArg List.length same))
        simp only [sourceEqual, sameLength, if_false, different]

def sourceMatchesViews (scope : Scope) (handle : Option Address) (memory : SourceMemory)
    (code input1 input2 output : SourceValue) : Option Bool :=
  match sourceRead scope handle with
  | none => some false
  | some observation => do
      let codeMatches ← sourceEqual memory code observation.request.inputs.code
      if !codeMatches then some false else do
      let input1Matches ← sourceEqual memory input1 observation.request.inputs.input1
      if !input1Matches then some false else do
      let input2Matches ← sourceEqual memory input2 observation.request.inputs.input2
      if !input2Matches then some false else
      sourceEqual memory output observation.output

def targetMatchesViews (scope : Scope) (handle : Option Address) (memory : TargetMemory)
    (code input1 input2 output : TargetValue) : Option Bool :=
  match targetRead scope handle with
  | none => some false
  | some observation =>
    match targetEqual memory code observation.request.inputs.code with
    | none => none
    | some false => some false
    | some true =>
      match targetEqual memory input1 observation.request.inputs.input1 with
      | none => none
      | some false => some false
      | some true =>
        match targetEqual memory input2 observation.request.inputs.input2 with
        | none => none
        | some false => some false
        | some true => targetEqual memory output observation.output

theorem matches_views_correspondence (scope : Scope) (handle : Option Address)
    (source : SourceMemory) (target : TargetMemory) (related : MemoryRelated source target)
    (code input1 input2 output : SourceValue) :
    targetMatchesViews scope handle target (encodeValue code) (encodeValue input1)
      (encodeValue input2) (encodeValue output) =
        sourceMatchesViews scope handle source code input1 input2 output := by
  simp only [targetMatchesViews, sourceMatchesViews, read_correspondence,
    equal_correspondence source target related]
  cases sourceRead scope handle with
  | none => rfl
  | some observation =>
    simp only
    cases codeRead : sourceEqual source code observation.request.inputs.code with
    | none => simp only [bind, Option.bind_none]
    | some codeMatch =>
      cases codeMatch with
      | false => simp [bind, Option.bind]
      | true =>
        simp only [bind, Option.bind_some, Bool.not_true,
          Bool.false_eq_true, if_false]
        cases input1Read : sourceEqual source input1 observation.request.inputs.input1 with
        | none => simp only [Option.bind_none]
        | some input1Match =>
          cases input1Match with
          | false => simp [Option.bind]
          | true =>
            simp only [Option.bind_some, Bool.not_true,
              Bool.false_eq_true, if_false]
            cases input2Read : sourceEqual source input2 observation.request.inputs.input2 with
            | none => simp only [Option.bind_none]
            | some input2Match => cases input2Match <;> simp [Option.bind]

theorem target_views_with_contents (scope : Scope) (handle : Option Address)
    (source : SourceMemory) (target : TargetMemory) (related : MemoryRelated source target)
    (code input1 input2 output : SourceValue) (bytes : Inputs) (outputBytes : List UInt8)
    (codeRead : NativeOps.ByteViews.sourceView source code = some bytes.code)
    (input1Read : NativeOps.ByteViews.sourceView source input1 = some bytes.input1)
    (input2Read : NativeOps.ByteViews.sourceView source input2 = some bytes.input2)
    (outputRead : NativeOps.ByteViews.sourceView source output = some outputBytes) :
    targetMatchesViews scope handle target (encodeValue code) (encodeValue input1)
        (encodeValue input2) (encodeValue output) =
      some (targetMatches scope handle bytes outputBytes) := by
  rw [matches_views_correspondence scope handle source target related]
  simp only [sourceMatchesViews, targetMatches, read_correspondence]
  cases sourceRead scope handle with
  | none => rfl
  | some observation =>
    simp only [equal_with_contents source code bytes.code _ codeRead,
      equal_with_contents source input1 bytes.input1 _ input1Read,
      equal_with_contents source input2 bytes.input2 _ input2Read,
      equal_with_contents source output outputBytes _ outputRead,
      bind, Option.bind_some]
    rw [byte_list_beq_comm bytes.code observation.request.inputs.code,
      byte_list_beq_comm bytes.input1 observation.request.inputs.input1,
      byte_list_beq_comm bytes.input2 observation.request.inputs.input2,
      byte_list_beq_comm outputBytes observation.output]
    cases (observation.request.inputs.code == bytes.code) <;>
      cases (observation.request.inputs.input1 == bytes.input1) <;>
      cases (observation.request.inputs.input2 == bytes.input2) <;> rfl

private def emptySource : SourceMemory := ⟨fun _ _ => none, fun _ => none⟩
private def emptyTarget : TargetMemory := ⟨fun _ _ => none, fun _ => none⟩
private def base : Address := ⟨1, 0, []⟩
private def firstByte : TargetMemory :=
  ⟨fun storage index => if storage = 1 ∧ index = 0 then some (.byte 1) else none,
    fun _ => none⟩

theorem null_nonempty_comparison_refuses_without_read :
    targetEqual emptyTarget (.array .byte none 1) [1] = some false := by decide +kernel

theorem length_mismatch_skips_missing_contents :
    targetEqual emptyTarget (.array .byte (some base) 2) [1] = some false := by decide +kernel

theorem byte_mismatch_skips_missing_tail :
    targetCompare firstByte base [2, 3] = some false := by decide +kernel

theorem equal_prefix_needs_live_tail :
    targetCompare firstByte base [1, 3] = none := by decide +kernel

theorem absent_receipt_skips_all_views :
    targetMatchesViews [] (some base) emptyTarget .unit .unit .unit .unit = some false := rfl

theorem empty_bytes_need_no_storage :
    sourceEqual emptySource (.array .byte none 0) [] = some true := rfl

end Mettapedia.GSLT.LanguageDef.NativeExecutionBytes
